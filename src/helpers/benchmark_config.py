'''
Created on 15.06.2014

@author: simon
'''
import os
import re

from architecture.guarded_system import GuardedArchitectureType


INT_RANGE_LIST_PATTERN = re.compile(r"(\d+:\d+)(,\d+:\d+)*")
INT_RANGE_LIST_ITEM_PATTERN = re.compile(r"(\d+):(\d+)")
INT_LIST_PATTERN = re.compile(r"(\d+)(,\d+)*")
INT_LIST_ITEM_PATTERN = re.compile(r"\d+")

NEGATED_FLAG_TEMPLATE = "no-%s"
LABEL_FLAG = "labels"
TEST_MODE_FLAG = "test"
SCC_FLAG = "scc"
DOT_FLAG = "dot"


class BenchmarkConfigException(Exception):
    def __init__(self, message):
        super().__init__(message)


class BenchmarkConfigItem:
    def __init__(self):
        self.filename = None
        self.guard_type = None
        self.instances = None
        self.min_bounds = None
        self.max_increment = None
        self.settings = None
        self.run_count = None

    def is_setting_active(self, name):
        if self.settings.__contains__(name):
            return True
        elif self.settings.__contains__(NEGATED_FLAG_TEMPLATE % name):
            return False
        raise BenchmarkConfigException("Setting '%s' is not specified "
                                       "for config item!" % name)


def parse_config_line(line, line_number, basedir):
    line = line.strip()
    if len(line) == 0 or line.startswith("#"):
        return None

    try:
        (filename,
         guard_type,
         instances,
         bounds,
         max_increment,
         settings,
         run_count) = line.split()
    except:
        raise BenchmarkConfigException("Invalid number of entries in "
                                       "configuration line %d!" % line_number)

    item = BenchmarkConfigItem()
    if os.path.isabs(filename):
        item.filename = filename
    else:
        item.filename = os.path.join(basedir, filename)

    item.guard_type = GuardedArchitectureType[guard_type]
    item.instances = _get_int_range_list(instances)
    item.min_bounds = _get_int_list(bounds)
    item.max_increment = int(max_increment)
    item.settings = settings.split(",")
    item.run_count = int(run_count)
    return item


def parse_config(content, basedir="."):
    lines = content.split(os.linesep)
    benchmarks = [parse_config_line(line, line_number, basedir)
                  for line_number, line in enumerate(lines)]
    benchmarks = [benchmark for benchmark in benchmarks
                  if benchmark is not None]
    return benchmarks


def read_config_file(config_path):
    config_dir = os.path.dirname(config_path)
    with open(config_path, 'r') as cfh:
        content = cfh.read()
    return parse_config(content, config_dir)


def _get_int_range_list(value):
    m = re.match(INT_RANGE_LIST_PATTERN, value)
    if m is None:
        raise BenchmarkConfigException("Invalid range list '%s'" % value)
    try:
        return [range(int(m[0]), int(m[1]) + 1)
                for m in re.findall(INT_RANGE_LIST_ITEM_PATTERN, value)]
    except:
        raise BenchmarkConfigException("Invalid range list '%s'" % value)


def _get_int_list(value):
    m = re.match(INT_LIST_PATTERN, value)
    if m is None:
        raise BenchmarkConfigException("Invalid integer list '%s'" % value)
    try:
        return [(int(m[0]))
                for m in re.findall(INT_LIST_ITEM_PATTERN, value)]
    except:
        raise BenchmarkConfigException("Invalid integer list '%s'" % value)
