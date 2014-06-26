#!/usr/local/bin/python2.7
# encoding: utf-8
'''
gp_bosy -- Guarded Parameterized Bounded Synthesis

gp_bosy is a prototype for the parameterized bounded synthesis of distributed
systems that communicate with each other by guards


:author:     Simon Ausserlechner, Ayrat Khalimov, Swen Jacobs

:copyright:  2014. All rights reserved.

:license:    Free for any use with references to the original authors.

'''

import sys
import os
import logging
import time

from argparse import ArgumentParser
from argparse import RawDescriptionHelpFormatter
from itertools import product
from multiprocessing import Process, Queue

from helpers.logging_helper import verbosity_to_log_level
from helpers.benchmark_config import read_config_file
from architecture.guarded_system import GuardedArchitecture
from bosy import BoundedSynthesis
from smt.encoder_base import SMTEncoder, EncodingOptimization
from helpers import benchmark_config
from visualization import dotvisualization
import config

__all__ = []
__version__ = 0.1
__date__ = '2014-06-15'
__updated__ = '2014-06-15'


class CLIError(Exception):
    '''Generic exception to raise and log different fatal errors.'''
    def __init__(self, msg):
        super(CLIError).__init__(type(self))
        self.msg = "E: %s" % msg

    def __str__(self):
        return self.msg

    def __unicode__(self):
        return self.msg


class BenchmarkRunException(Exception):
    def __init__(self, message):
        super().__init__(message)


class BenchmarkTestRequest(object):
    def __init__(self):
        self.spec_filepath = None
        self.guard_type = None
        self.instance_count = None
        self.min_bound = None
        self.max_increment = None
        self.settings = None
        self.save_dot = None
        self.dot_directory = None

        self.use_label_guards = None
        self.use_test_mode = None
        self.use_scc = None

        self.benchmark_index = None
        self.run_index = None

    @property
    def dot_filepath(self):

        return os.path.join(self.dot_directory,
                            config.BENCHMARK_DOT_FILENAME.format(
                                spec_name=self.dot_name,
                                benchmark_index=self.benchmark_index,
                                run_index=self.run_index))

    @property
    def dot_name(self):
        spec_filename = os.path.basename(self.spec_filepath)
        return os.path.splitext(spec_filename)[0]


class BenchmarkTestResult(object):
    def __init__(self):
        self.request = None
        self.runtime = None
        self.is_satisfiable = None
        self.current_bound = None
        self.description = None

    @property
    def current_bound_sum(self):
        return sum(self.current_bound)

    @property
    def satisfiability(self):
        return ["unsat", "sat"][self.is_satisfiable]


class BenchmarkTestControllerResult(BenchmarkTestResult):
    def __init__(self, request):
        super().__init__()
        self.request = request
        self.runtime = "N/A"
        self.is_satisfiable = "N/A"
        self.current_bound = "N/A"

    @property
    def current_bound_sum(self):
        return "N/A"

    @property
    def satisfiability(self):
        return "N/A"


class BenchmarkTestTimeoutResult(BenchmarkTestControllerResult):
    def __init__(self, request):
        super().__init__(request)
        self.runtime = "TIMEOUT"


class BenchmarkTestInvalidExitResult(BenchmarkTestControllerResult):
    def __init__(self, request, exit_code):
        super().__init__(request)
        self.description = "Exit code: %s" % exit_code


def _execute_benchmark_test(queue):
    try:
        log = logging.getLogger("bm-runner")
        request = queue.get()

        arch_type = GuardedArchitecture.get_type_by_id(request.guard_type)
        bosy = BoundedSynthesis(request.spec_filepath, arch_type)
        templates_count = bosy.spec.templates_count
        bosy.min_bound = tuple(request.min_bound * templates_count
                               if len(request.min_bound) == 1
                               else request.min_bound)

        bosy.max_increments = request.max_increment

        # set number of instances
        instance_count = request.instance_count
        if len(instance_count) > 1 and len(instance_count) != templates_count:
            raise BenchmarkRunException(
                "Invalid number of instances: Please provide a "
                "number of instances for each template")
        if sum(instance_count) < 2:
            raise BenchmarkRunException(
                "Invalid number of instances: Please provide an "
                "overall instance number of at least 2.")
        bosy.instance_count = tuple(instance_count * templates_count
                                    if len(instance_count) == 1
                                    else instance_count)

        # set other parameters
        bosy.encoder_type = \
            [SMTEncoder.STATE_GUARD_ENCODER,
             SMTEncoder.LABEL_GUARD_ENCODER][request.use_label_guards]
        bosy.test_mode = request.use_test_mode
        bosy.encoder_optimization = \
            [EncodingOptimization.NONE,
             EncodingOptimization.LAMBDA_SCC][request.use_scc]

        t = time.clock()
        model = bosy.solve()
        t = time.clock() - t
        try:
            if model is not None and request.save_dot:
                dotvisualization.model_to_dot(
                    model, request.dot_filepath,
                    name=request.dot_name)
                log.debug("Wrote dot file to '%s'" % request.dot_filepath)
        except Exception as ex:
            log.critical("Could not write model graph: %s", ex)

        result = BenchmarkTestResult()
        result.request = request
        result.runtime = t
        result.current_bound = bosy.spec.bound
        result.is_satisfiable = (model is not None)
        queue.put(result)
    except Exception as ex:
        queue.put(ex)
        sys.exit(1)


class BenchmarkExecution:
    def __init__(self, config_filepaths, csv_filepath, log_filepath,
                 dot_directory, timeout=None):
        self._csv_filepath = csv_filepath
        self._log_filepath = log_filepath
        self._dot_directory = dot_directory
        self._timeout = timeout
        self._log = logging.getLogger("bm-ctrl")
        self._benchmark_index = 0

        self._benchmarks = []
        for config_path in config_filepaths:
            benchmark_config = read_config_file(config_path)
            self._benchmarks.append((config_path, benchmark_config))

    def _execute_benchmark(self, benchmark_item):
        instance_counts = product(*benchmark_item.instances)
        min_bounds = [benchmark_item.min_bounds]  # product(*benchmark_item.min_bounds)

        for instance_count in instance_counts:
            for min_bound in min_bounds:
                self._benchmark_index += 1
                invalid_run = False
                run_index = 0
                while not invalid_run and run_index < benchmark_item.run_count:
                    # start test
                    queue = Queue()
                    request = self._get_benchmark_request(benchmark_item,
                                                     instance_count,
                                                     min_bound)
                    request.benchmark_index = self._benchmark_index
                    request.run_index = run_index
                    queue.put(request)

                    proc = Process(target=_execute_benchmark_test,
                                   args=(queue,))
                    proc.start()
                    proc.join(self._timeout)

                    if proc.is_alive():
                        proc.terminate()
                        proc.join()
                        result = BenchmarkTestTimeoutResult(request)
                        invalid_run = True
                    elif queue.empty():
                        result = BenchmarkTestInvalidExitResult(request,
                                                                proc.exitcode)
                        invalid_run = True
                    else:
                        result = queue.get()

                    if isinstance(result, Exception):
                        self._log.critical(result)

                    self._report_benchmark_result(request, result)
                    run_index += 1
                self._log.debug("Finished runs for spec %s, "
                                "instance count %s, bound %s "
                                "(invalid run: %s)",
                                os.path.basename(benchmark_item.filename),
                                str(instance_count), str(min_bound),
                                ["no", "yes"][invalid_run])

    def _get_benchmark_request(self, benchmark_item,
                               instance_count,
                               min_bound):
        request = BenchmarkTestRequest()
        request.dot_directory = self._dot_directory
        request.save_dot = \
            benchmark_item.is_setting_active(benchmark_config.DOT_FLAG)
        request.guard_type = benchmark_item.guard_type
        request.instance_count = instance_count
        request.max_increment = benchmark_item.max_increment
        request.min_bound = min_bound
        request.spec_filepath = benchmark_item.filename

        request.use_label_guards = \
            benchmark_item.is_setting_active(benchmark_config.LABEL_FLAG)
        request.use_scc = \
            benchmark_item.is_setting_active(benchmark_config.SCC_FLAG)
        request.use_test_mode = \
            benchmark_item.is_setting_active(benchmark_config.TEST_MODE_FLAG)

        return request

    def execute_benchmarks(self):
        for config_filepath, benchmark_items in self._benchmarks:
            self._log.info("Start benchmarks for '%s'", config_filepath)

            for benchmark_item in benchmark_items:
                self._execute_benchmark(benchmark_item)

            self._log.info("Finished benchmarks for '%s'", config_filepath)

    def _report_benchmark_result(self, request, result=None):
        cols = [""] * 15
        cols[0] = str(request.benchmark_index)
        cols[1] = str(request.run_index)
        cols[2] = os.path.basename(request.spec_filepath)
        cols[3] = str(request.instance_count)
        cols[4] = str(sum(request.instance_count))
        cols[5] = str(request.min_bound)
        cols[6] = str(sum(request.min_bound))
        cols[7] = ["no-labels", "labels"][request.use_label_guards]
        cols[8] = ["no-scc", "scc"][request.use_scc]
        cols[9] = ["no-test", "test"][request.use_test_mode]

        if isinstance(result, BenchmarkTestResult):
            cols[10] = str(result.current_bound)
            cols[11] = str(result.current_bound_sum)
            cols[12] = result.satisfiability
            cols[13] = str(result.runtime)
            if result.description is not None:
                cols[14] = str(result.description)
        else:
            cols[14] = str(result)

        line = ";".join(cols)

        with open(self._csv_filepath, 'a+') as csv_fh:
            csv_fh.write(line)
            csv_fh.write(os.linesep)


def get_argparser():
    program_version = "v%s" % __version__
    program_build_date = str(__updated__)
    program_version_message = '%%(prog)s %s (%s)' % (program_version,
                                                     program_build_date)
    program_shortdesc = __import__('__main__').__doc__.split("\n")[1]
    program_license = '''%s

  Created by simon, ayrat, swen on %s.
  Copyright 2014 organization_name. All rights reserved.

  Licensed under the Apache License 2.0
  http://www.apache.org/licenses/LICENSE-2.0

  Distributed on an "AS IS" basis without warranties
  or conditions of any kind, either express or implied.

USAGE
''' % (program_shortdesc, str(__date__))

    # Setup argument parser
    parser = ArgumentParser(description=program_license,
                            formatter_class=RawDescriptionHelpFormatter)
    parser.add_argument("-v", "--verbose", dest="verbose",
                        action="count",
                        help="set verbosity level [default: %(default)s]")
    parser.add_argument("-l", "--log-path", dest="log_path",
                        help="log path")
    parser.add_argument("-c", "--csv-path", dest="csv_path", required=True,
                        help="csv path")
    parser.add_argument('-V', '--version', action='version',
                        version=program_version_message)
    parser.add_argument('-d', '--dot-path', dest="dot_path", required=True,
                        help="directory where dot files should be stored")
    parser.add_argument('-t', '--timeout', type=int,
                        default=None, dest="timeout",
                        help="timeout for a single test run "
                        "[default: %(default)s]")
    parser.add_argument(dest="paths",
                        help="paths to configuration file(s)", nargs='+')
    return parser


def main(argv=None):
    '''Command line options.'''

    if argv is None:
        argv = sys.argv
    else:
        sys.argv.extend(argv)

    try:
        parser = get_argparser()
        # Process arguments
        args = parser.parse_args()
        paths = args.paths
        verbose = args.verbose
        log_path = args.log_path
        csv_path = args.csv_path
        timeout = args.timeout
        dot_path = args.dot_path

        level = verbosity_to_log_level(verbose)
        print("Log level is '%s'" % logging.getLevelName(level))
        logging.basicConfig(level=level, pathname=log_path,
                            format=config.LOG_FORMAT)

        benchmark_exec = BenchmarkExecution(paths, csv_path, log_path,
                                            dot_path, timeout)
        benchmark_exec.execute_benchmarks()

        return 0
    except KeyboardInterrupt:
        ### handle keyboard interrupt ###
        return 0

if __name__ == "__main__":
    sys.exit(main())
