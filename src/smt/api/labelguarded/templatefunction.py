'''
Created on 24.05.2014

@author: simon
'''
from z3 import Function, BoolSort, Bool, If, BitVecVal, \
               BitVecSort, Const, ForAll, RotateLeft
from functools import reduce

from smt.api import templatefunction


class TemplateFunction(templatefunction.TemplateFunction):
    def __init__(self, template, encoder, encoder_info, spec):
        self.aux_labels = None
        self.aux_label_switches = None
        self.guard_bit_offset = None
        self._num_aux_vars = None
        super().__init__(template, encoder, encoder_info, spec)

    def _define_state_guard(self):
        self._num_aux_vars = self._encoder_info.guard_slice_sizes[
            self._template.template_index] - self.num_label_guard_vars

        assert self._num_aux_vars >= 0

        # define label to bitvec bit
        self._define_aux_labels()
        self._define_label_values()

    def _define_aux_labels(self):
        self.aux_labels = [Function("aux_%s_%s" % (self.template_index, i),
                                    self.state_sort, BoolSort())
                           for i in range(self._num_aux_vars)]

        self.aux_label_switches = [Bool("use_aux_%s_%s" %
                                        (self.template_index, i))
                                   for i in range(self._num_aux_vars)]

    def _define_label_values(self):
        """
        Defines the function label values

        guard_state_bit: T -> BitVec(Sum_i(2**|O_i+use_aux_labels*|T_i||))
        Returns the bit vector corresponding to a given state's labels
        """
        function_arguments = [self.state_sort,
                              BitVecSort(self._encoder_info.guard_size)]
        function_declaration = Function('label_values_%d' %
                                        self._template.template_index,
                                        function_arguments)

        self.guard_bit_offset = sum(self._encoder_info.guard_slice_sizes
                                    [:self._template.template_index])

        # ensures that each output label and its negation have a unique bit
        # in the bit vector
        t_i = Const('ti', self.state_sort)
        body_exprs = [If(self.output_functions[i](t_i),
                         BitVecVal(1 << (self.guard_bit_offset + i),
                                   self._encoder_info.guard_size), 0)
                      for i in range(0, len(self.output_functions))]

        # the same is ensured for the additional auxiliary labels
        # aux_offset = self.guard_bit_offset + 2 * len(self.output_functions)

        function_body = reduce(lambda x, y: x | y, body_exprs)

        self._encoder_info.solver.append(
            ForAll(t_i, function_declaration(t_i) == RotateLeft(1, function_body)))
        self.state_guard = function_declaration

    @property
    def output_aux_functions(self):
        return self.output_functions + self.aux_labels

    @property
    def num_label_guard_vars(self):
        return 2 ** len(self.output_functions)
