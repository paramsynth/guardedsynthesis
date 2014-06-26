'''
Created on 24.05.2014

@author: simon
'''
from z3 import Function, BitVecSort, BitVecVal, Const, ForAll, Implies, And

from smt.api import templatefunction


class TemplateFunction(templatefunction.TemplateFunction):
    '''
    Encapsulates functionality that is required for synthesis based
    on state guards
    '''
    def __init__(self, template, encoder, encoder_info, spec):
        super().__init__(template, encoder, encoder_info, spec)

    def _define_state_guard(self):
        # guard state to bitvec bit
        self._define_guard_state_bit()

    def _define_guard_state_bit(self):
        """
        Defines the function guard_state_bit

        guard_state_bit: T -> BitVec(Sum_i(T_i|))
        Returns the bit vector corresponding to a given state
        """
        function_arguments = [self.state_sort, BitVecSort(self._spec.bound_sum)]
        function_declaration = \
            Function('guard_state_bit_%d' % (self._template.template_index),
                     function_arguments)

        local_bound = self._template.bound
        spec_bound = self._encoder.spec.bound
        bit_offset = sum(spec_bound[:self._template.template_index])
        bit_length = local_bound

        # TODO: use bit masks
        # mask: all ones - ones except for lower parts +
        #       ones for parts below offset
        mask_value = \
            ((1 << self._spec.bound_sum) - 1) - \
            ((1 << (bit_offset + bit_length)) - 1) + \
            ((1 << bit_offset) - 1)
        mask = BitVecVal(mask_value, self._spec.bound_sum)

        # assertions for function
        t_i = Const('ti', self.state_sort)
        t_j = Const('tj', self.state_sort)
        self._encoder_info.solver.add(
            ForAll(
                [t_i, t_j],
                Implies(
                    t_i != t_j,
                    (function_declaration(t_i) & function_declaration(t_j)) ==
                    BitVecVal(0, self._spec.bound_sum))))

        self._encoder_info.solver.add(
            ForAll(
                [t_i],
                And((function_declaration(t_i) & mask ==
                     BitVecVal(0, self._spec.bound_sum)),
                    (function_declaration(t_i) !=
                     BitVecVal(0, self._spec.bound_sum)))))
        self.state_guard = function_declaration
