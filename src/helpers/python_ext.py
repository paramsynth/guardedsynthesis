from collections import Iterable
import math
from itertools import cycle, islice


def roundrobin(iterables):
    '''
    source:
    http://stackoverflow.com/questions/11125212/interleaving-lists-in-python
    https://docs.python.org/2/library/itertools.html#recipes
    Recipe credited to George Sakkis
    
    
    roundrobin('ABC', 'D', 'EF') --> A D E B F C
    
    :author: simon
    '''
    pending = len(iterables)
    nexts = cycle(iter(it).next for it in iterables)
    while pending:
        try:
            for next in nexts:
                yield next()
        except StopIteration:
            pending -= 1
            nexts = cycle(islice(nexts, pending))

def to_str(enumerable:Iterable) -> str:
    return ', '.join(map(str, enumerable))


def lmap(lambda_func, iterable) -> list:
    return list(map(lambda_func, iterable))


def lfilter(lambda_func, iterable) -> list:
    return list(filter(lambda_func, iterable))


def add_dicts(*dicts) -> dict:
    resulting_items = []
    for d in dicts:
        resulting_items += list(d.items())
    return dict(resulting_items)


def get_add(dict, name, default):
    res = dict[name] = dict.get(name, default)
    return res


def is_empty_str(s):
    return s is None or s == ''


def bin_fixed_list(i, width):
    """ Return list of boolean values """
    assert i >= 0, str(i)
    assert i <= math.pow(2, width) - 1, str(i)

    bits = [bool(b != '0') for b in bin(i)[2:]]
    extension_size = width - len(bits)

    assert extension_size >= 0, str(extension_size)

    extended_bits = [False] * extension_size + bits
    return extended_bits


def index_of(lambda_func, iterable):
    for (i, e) in enumerate(iterable):
        if lambda_func(e):
            return i
    return None


class StrAwareList(Iterable):
    def __init__(self, output=None):
        if output is None:
            output = []
        self._output = output

    def __str__(self):
        if self._output.__class__ == list:
            return '\n'.join(self._output)
        else:
            return str(self._output)

    __repr__ = __str__

    def __len__(self):
        try:
            return getattr(self._output, "__len__")()
        except AttributeError:
            return 0

    def __iter__(self):
        for e in self._output:
            yield e

    def __iadd__(self, other):
        self.__add__(other)
        return self

    def __add__(self, other):
        if isinstance(other, Iterable) and not isinstance(other, str) and not isinstance(other, bytes):
            self._output.extend(other)
            return self
        else:
            self._output.append(other)
            return self


class FileWithAppendExtend:
    def __init__(self, file_writer):
        self._file_writer = file_writer
        self._len = 0

    def append(self, str):
        self._file_writer.write(str)
        self._file_writer.write('\n')
        self._len += 1

    def extend(self, strings):
        for s in strings:
            self.append(s)

    def __len__(self):
        return self._len
