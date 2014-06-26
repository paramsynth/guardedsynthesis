"""
Python visitor pattern

source: http://curtis.schlak.com/2012/01/04/python-visitor-pattern-helper.html
"""
# visit.py


import inspect

__all__ = ['on', 'when']


def on(param_name):
    def f(fn):
        dispatcher = Dispatcher(param_name, fn)
        return dispatcher
    return f


def when(param_type):
    def f(fn):
        frame = inspect.currentframe().f_back
        dispatcher = frame.f_locals[fn.__name__]
        if not isinstance(dispatcher, Dispatcher):
            dispatcher = dispatcher.dispatcher
        dispatcher.add_target(param_type, fn)
        def ff(*args, **kw):
            return dispatcher(*args, **kw)
        ff.dispatcher = dispatcher
        return ff
    return f


class Dispatcher(object):
    def __init__(self, param_name, fn):
        frame = inspect.currentframe().f_back.f_back
        top_level = frame.f_locals == frame.f_globals
        # pylint: disable=no-member
        self.param_index = inspect.getfullargspec(fn).args.index(param_name)
        self.param_name = param_name
        self.targets = {}

    def __call__(self, *args, **kw):
        typ = args[self.param_index].__class__  # BUG FIX: use __class__ here
        d = self.targets.get(typ)
        if d is not None:
            return d(*args, **kw)
        else:
            issub = issubclass
            t = self.targets
            ks = t.keys()
            res = [t[k](*args, **kw) for k in ks if issub(typ, k)]
            if len(res) == 1:
                return res[0]
            return res

    def add_target(self, typ, target):
        self.targets[typ] = target
