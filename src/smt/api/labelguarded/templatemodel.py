'''
Created on 15.05.2014

@author: simon
'''
from z3 import is_true, And

from smt.api.templatemodel import ApiTemplateModel


class LabelGuardedTemplateModel(ApiTemplateModel):
    def __init__(self, model, templatefunction):
        super().__init__(model, templatefunction)

        bit_offset = templatefunction.guard_bit_offset

        # get for each guard bit the conjuncts which must be satisfied
        # by the particular state outputs such that the state
        # represents the considered guard bit
        guard_output_funcs = \
            {i: self._get_output_functions(i)
             for i in range(templatefunction.num_label_guard_vars)}

        # check whether state matches guard label
        def _state_matches_guard(t, i):
            expr = And([func_call(t) == func_res
                        for func_call, func_res in guard_output_funcs[i]])
            return is_true(model.eval(expr))

        self.output_bit_state_dict = \
            {2 ** (bit_offset + i):
             [str(t) for t in self._internal_states if _state_matches_guard(t, i)]
             for i in range(templatefunction.num_label_guard_vars)}

    def _get_output_functions(self, guard_bit):
        bit_assignment = guard_bit
        guard_conjuncts = \
            [(func, bit_assignment & (1 << i) > 0)
             for i, func in
             enumerate(self._template_function.output_aux_functions)]
        return guard_conjuncts

    def _num_to_label_guard(self, num_guard, bits_state_dict):
        guard_set = set()
        for k, v in bits_state_dict.items():
            if num_guard & k:
                guard_set.update(v)
        return "{%s}" % ",".join(sorted(list(guard_set)))

    def init_labeled_transitions(self, bits_state_dict):
        self.transitions = {k: self._num_to_label_guard(num_guard,
                                                        bits_state_dict)
                            for k, num_guard in self.num_guards.items()}
