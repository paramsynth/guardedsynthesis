#!/bin/env python3
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

from argparse import ArgumentParser
from argparse import RawDescriptionHelpFormatter
import logging
from bosy import BoundedSynthesis
from smt.encoder_base import SMTEncoder, EncodingOptimization
import time
from architecture import guarded_system
from visualization.dotvisualization import model_to_dot
import config
import helpers
from architecture.guarded_system import GuardedArchitectureType

__all__ = []
__version__ = 0.1
__date__ = '2014-05-01'
__updated__ = '2014-05-01'

DEBUG = 1


class CLIError(Exception):
    '''Generic exception to raise and log different fatal errors.'''
    def __init__(self, msg):
        super(CLIError).__init__(type(self))
        self.msg = "E: %s" % msg

    def __str__(self):

        return self.msg

    def __unicode__(self):
        return self.msg


def main(argv=None):
    '''Command line options.'''

    if argv is None:
        argv = sys.argv
    else:
        sys.argv.extend(argv)

    program_name = os.path.basename(sys.argv[0])
    program_version = "v%s" % __version__
    program_build_date = str(__updated__)
    program_version_message = '%%(prog)s %s (%s)' % (program_version,
                                                     program_build_date)
    program_shortdesc = __import__('__main__').__doc__.split("\n")[1]
    program_license = '''%s

  Created by simon, ayrat, swen on %s.
  Copyright 2014. All rights reserved.

  Free for any use with references to the original authors.

  Distributed on an "AS IS" basis without warranties
  or conditions of any kind, either express or implied.

USAGE
''' % (program_shortdesc, str(__date__))

    try:
        # Setup argument parser
        parser = ArgumentParser(description=program_license,
                                formatter_class=RawDescriptionHelpFormatter)
        parser.add_argument("ltl_filepath", type=str,
                            help="path of ltl specification file")
        parser.add_argument("-v", "--verbose", dest="verbose", action="count",
                            help="set verbosity level [default: %(default)s]")
        parser.add_argument("--dot-path", dest="dot_path", type=str,
                            default=config.DEFAULT_TARGET_FOLDER,
                            help="Default dot file path, relative to spec "
                            "file or absolute [default: %(default)s]")
        parser.add_argument("-t", "--system-type", dest="system_type",
                            help=("System type (conjunctive, disjunctive) "
                                  "[default: %(default)s]"),
                            default="conjunctive")
        parser.add_argument("--min-bound", dest="min_bound",
                            help=("Minimal template size for each template "
                                  "[default: %(default)s]"),
                            type=int, default=2, nargs="+")
        parser.add_argument("--max-increments", dest="max_increments",
                            help=("Maximal number of increments of template "
                                  "bounds [default: %(default)s]"),
                                  type=int, default=1024)
        parser.add_argument("--instances", dest="instance_count",
                            help="Number of instances for each template",
                            type=int, nargs="+", required=True)
        parser.add_argument('-V', '--version', action='version',
                            version=program_version_message)
#         parser.add_argument('--smt2', action='store_true',
#                             help="Use SMT2 encoder [default: %(default)s]",
#                             default=False)
        parser.add_argument('--test', action='store_true',
                            help=("Use test mode (ignore cut-offs) "
                                  "[default: %(default)s]"), default=False)
        parser.add_argument("--optimization", action='store_true',
                            help=("Use encoding optimizations "
                                  "[default: %(default)s]"), default=False)
        parser.add_argument('--label-guards', dest="label_guards",
                            action='store_true',
                            help=("Synthesize label guards "
                                  "instead of state guards"))

        args = parser.parse_args()

        logging.basicConfig(
            level=helpers.logging_helper.verbosity_to_log_level(args.verbose))
        print("Log level: %s" % logging.getLevelName(
                  logging.getLogger().getEffectiveLevel()))

        # setup bounded synthesis instance

        ltl_filepath = args.ltl_filepath
        arch_type = guarded_system.GuardedArchitecture.get_type_by_id(
            GuardedArchitectureType[args.system_type])

        if arch_type is None:
            sys.exit("Invalid system type")

        bosy = BoundedSynthesis(ltl_filepath, arch_type)

        # set minimal bound
        min_bound = args.min_bound
        templates_count = bosy.spec.templates_count
        if len(min_bound) > 1 and len(min_bound) != templates_count:
            sys.exit("Invalid number of minimal templates bound")
        bosy.min_bound = tuple(min_bound * templates_count
                               if len(min_bound) == 1 else min_bound)

        max_increments = args.max_increments
        bosy.max_increments = max_increments

        # set number of instances
        instance_count = args.instance_count
        if len(instance_count) > 1 and len(instance_count) != templates_count:
            sys.exit("Invalid number of instances: Please provide a "
                     "number of instances for each template")
        if sum(instance_count) < 2:
            sys.exit("Invalid number of instances: Please provide an "
                     "overall instance number of at least 2.")
        bosy.instance_count = tuple(instance_count * templates_count
                                    if len(instance_count) == 1
                                    else instance_count)

        # set other parameters
        bosy.encoder_type = [SMTEncoder.STATE_GUARD_ENCODER,
                             SMTEncoder.LABEL_GUARD_ENCODER][args.label_guards]
        bosy.test_mode = args.test
        bosy.encoder_optimization = [EncodingOptimization.NONE,
                                     EncodingOptimization.LAMBDA_SCC][args.optimization]

        print("Start finding a solution for problem \'%s\'" % bosy.spec_filename)
        print("Number of templates: %s" % str(bosy.spec.templates_count))
        print("Minimal bound:       %s" % str(bosy.min_bound))
        print("Maximal increments:  %s" % str(bosy.max_increments))
        print("Number of instances: %s" % str(bosy.instance_count))
        print("System type:         %s" % str(args.system_type))

        t = time.clock()

        model = bosy.solve()

        elapsed_time = time.clock() - t

        print("==============================================================")
        print("Initial bound was %s; "
              "current bound is %s" % (str(bosy.min_bound),
                                       str(bosy.spec.bound)))
        print("Status: " + ["model found", "no model found"][model is None])
        if model is not None:
            print("\n".join([str(template_model)
                             for template_model in model.values()]))
        print("Elapsed time: %ss" % elapsed_time)
        print("==============================================================")

        dot_path = args.dot_path
        if model is not None and dot_path is not None:
            # extend by directory of specification if relative
            if not os.path.isabs(dot_path):
                dot_path = os.path.join(os.path.dirname(args.ltl_filepath),
                                        dot_path)
            # if directory, we need to specify the filename
            if not os.path.basename(dot_path):
                spec_name = os.path.splitext(
                    os.path.basename(args.ltl_filepath))[0]
                filename = config.DEFAULT_DOT_FILENAME.format(
                    spec_name=spec_name)
                dot_path = os.path.join(dot_path, filename)

            model_to_dot(model, dot_path)

        return 0
    except Exception as ex:
        if DEBUG:
            raise(ex)
        indent = len(program_name) * " "
        sys.stderr.write(program_name + ": " + repr(ex) + "\n")
        sys.stderr.write(indent + "  for help use --help")
        return 2

if __name__ == "__main__":
    sys.exit(main())
