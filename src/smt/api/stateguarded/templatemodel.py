'''
Created on 15.05.2014

@author: simon
'''
from smt.api.templatemodel import ApiTemplateModel


class StateGuardedTemplateModel(ApiTemplateModel):
    '''
    Stores label-guarded synthesis results for one particular template
    '''
    def __init__(self, model, templatefunction):
        super().__init__(model, templatefunction)

        # retrieve the bit assignments of the different states
        self.guard_state_bits = \
            {self.model.evaluate(
                self._template_function.state_guard(state)).as_long():
             str(state) for state in self._internal_states}

    def apply_guard_state_bit_dictionary(self, bit_to_state_dict):
        '''
        Replaces the numeric guard set information by state name strings
        as defined by the bit_to_state_dict dictionary.

        :param bit_to_state_dict:
        '''

        def to_set(value):
            states = set()
            for bit, state in bit_to_state_dict.items():
                if value & bit:
                    states.add(state)
            return states

        self.transitions = {k: to_set(v) for k, v in self.num_guards.items()}

    def _get_sorted_guard_bits_str(self):
        return "{%s}" % ", ".join(["%s: %s" % (val, state)
                                   for val, state in
                                   sorted(self.guard_state_bits.items())])
