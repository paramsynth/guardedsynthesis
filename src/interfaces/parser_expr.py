from helpers.python_ext import index_of
from functools import lru_cache


class Signal:
    def __init__(self, name:str):
        self.name = name
        self.__hash_value = hash(self.name)

    def __repr__(self):
        return str(self.name)

    def __eq__(self, other):
        if not isinstance(other, Signal):
            return False
        return self.name == other.name

    def __hash__(self):
        return self.__hash_value


class TemplateSignal(Signal):
    def __init__(self, base_name:str, template_index:int):
        super().__init__(base_name)
        self.template_index = template_index

        self.__cached_str = self.name + '_' + str(template_index)
        self.__hash_value = hash(self.__cached_str)

    def __repr__(self):
        return self.__cached_str

    def __hash__(self):
        return self.__hash_value

    def __eq__(self, other):
        if not isinstance(other, TemplateSignal):
            return False
        return self.__cached_str == other.__cached_str

    __str__ = __repr__

    @lru_cache()
    def get_instance_signal(self, instance_index:int):
        return InstanceSignal(self.name, self.template_index, instance_index)


class InstanceSignal(Signal):
    def __init__(self, base_name:str, template_index:int, instance_index:int):
        super().__init__(base_name)
        self.template_index = template_index
        self.instance_index = instance_index

        self.__cached_str = '%s_%d_%d' % (self.name, template_index, instance_index)
        self.__hash_value = hash(self.__cached_str)

    def __repr__(self):
        return self.__cached_str

    def __hash__(self):
        return self.__hash_value

    def __eq__(self, other):
        if not isinstance(other, InstanceSignal):
            return False
        return self.__cached_str == other.__cached_str

    __str__ = __repr__


class QuantifiedSignal(Signal):
    def __init__(self, base_name:str, binding_indices:tuple):
        super().__init__(base_name)
        self.binding_indices = tuple(binding_indices)  # binding index: str means parametrization, int - process index

        self.__cached_str = self.name + '_' + '_'.join(map(str, self.binding_indices))
        self.__hash_value = hash(self.__cached_str)

    def __repr__(self):
        return self.__cached_str

    def __hash__(self):
        return self.__hash_value

    def __eq__(self, other):
        if not isinstance(other, QuantifiedSignal):
            return False
        return self.__cached_str == other.__cached_str

    __str__ = __repr__


class QuantifiedTemplateSignal(QuantifiedSignal):
    '''
    Represents a signal that contains a quantified index and belongs to
    a specific template

    :author: simon
    '''
    def __init__(self, base_name:str, template_index:int, *binding_indices):
        super().__init__(base_name, binding_indices)
        self.template_index = template_index

        self.__cached_str = self.name + '_' + str(template_index) + '_' + '_'.join(map(str, self.binding_indices))
        self.__hash_value = hash(self.__cached_str)

    def __repr__(self):
        return self.__cached_str

    def __hash__(self):
        return self.__hash_value

    def __eq__(self, other):
        if not isinstance(other, QuantifiedTemplateSignal):
            return False
        return self.__cached_str == other.__cached_str

    __str__ = __repr__


class QuantifiedTemplateSchedulerSignal(QuantifiedTemplateSignal):
    '''
    Template signal that represents the is_scheduled signal from the
    LTL specification

    :author: simon
    '''
    def __init__(self, template_index, *binding_indices):
        super().__init__('is_scheduled', template_index, *binding_indices)

        self.__cached_str = \
            self.name + '_' + \
            str(template_index) + '_' + \
            '_'.join(map(str, self.binding_indices))
        self.__hash_value = hash(self.__cached_str)

    def __repr__(self):
        return self.__cached_str

    def __hash__(self):
        return self.__hash_value

    def __eq__(self, other):
        if not isinstance(other, QuantifiedTemplateSchedulerSignal):
            return False
        return self.__cached_str == other.__cached_str

    __str__ = __repr__


class Number:
    def __init__(self, number:int):
        self._number = number

    def __repr__(self):
        return str(self._number)

    def __eq__(self, other):
        if not isinstance(other, Number):
            return False
        return self._number == other._number

    def __ne__(self, other):
        return not self.__eq__(other)


class Expr:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return str(self.name)

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        if not isinstance(other, self.__class__):
            return False
        return str(self) == str(other)


class Bool(Expr):
    def __init__(self, value):
        super().__init__(str(value))

    def __repr__(self):
        return self.name


class BinOp(Expr):
    def __init__(self, name, arg1, arg2):
        super().__init__(name)
        self.arg1 = arg1
        self.arg2 = arg2

    def __repr__(self):
        if self.name != '=':
            return str(self.arg1) + ' ' + self.name + ' ' + str(self.arg2)
        else:
            return str(self.arg1) + self.name + str(self.arg2)


class UnaryOp(Expr):
    def __init__(self, name, arg):
        super().__init__(name)
        self.arg = arg

    def __repr__(self):
        return self.name + '({0})'.format(self.arg)


class ForallExpr(Expr):
    def __init__(self, binding_indices:'binding indices', expr:Expr):
        super().__init__('Forall')
        self.arg1, self.arg2 = tuple(binding_indices), expr  # TODO: rename fields

    @property
    def binding_indices(self):
        return self.arg1

    def __str__(self):
        return self.name + str('({0})'.format(','.join(self.arg1))) + ' ' + str(self.arg2)


    __repr__ = __str__


########################################################################################
# helpers

def and_expressions(conjuncts):
    conjuncts = [c for c in conjuncts if c != Bool(True)]

    if len(conjuncts) == 0:
        return Bool(True)

    if len(conjuncts) == 1:
        return conjuncts[0]

    res = conjuncts[0]
    for c in conjuncts[1:]:
        res = BinOp('*', res, c)

    return res


def is_quantified_property(property) -> Bool:  # TODO: does not allow embedded forall quantifiers
    """ Return True iff the property has quantified indices.
        Numbers cannot be used as quantification indices.
    """
    for e in property.assumptions + property.guarantees:
        if isinstance(e, ForallExpr):
            binding_indices = e.arg1
            if index_of(lambda bi: isinstance(bi, str), binding_indices) is not None:
                return True
        else:
            assert e.__class__ in [ForallExpr, BinOp, UnaryOp, Bool], 'unknown class'

    return False
