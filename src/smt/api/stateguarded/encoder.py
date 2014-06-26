'''
Created on 15.05.2014

@author: simon
'''
import logging

from z3 import sat

from smt.api.encoder import PyZ3Encoder
from smt.encoder_base import SMTEncoder
from smt.api.stateguarded.templatemodel import StateGuardedTemplateModel



class StateGuardedPyZ3Encoder(PyZ3Encoder):
    '''
    Encoder for synthesis of state based guards
    '''

    @classmethod
    def get_encoder_type(cls):
        return SMTEncoder.STATE_GUARD_ENCODER

    def _init_guard_size(self):
        self.encoder_info.guard_size = self.spec.bound_sum

    def _encode_template_functions(self):
        # create templates
        from smt.api.stateguarded.templatefunction import TemplateFunction
        self.encoder_info.template_functions = [
                TemplateFunction(template, self, self.encoder_info, self.spec)
                for template in self.spec.templates]

    def check(self):
        s = self.encoder_info.solver
        res = s.check()
        model = None
        is_sat = res == sat
        if is_sat:
            model = {}
            guard_bits = {}
            for t in self.encoder_info.template_functions:
                template_model = StateGuardedTemplateModel(s.model(), t)
                guard_bits.update(template_model.guard_state_bits)
                model[t.template_index] = template_model
            for template_model in model.values():
                template_model.apply_guard_state_bit_dictionary(guard_bits)
        logging.info("Solver result: %s", res)
        logging.debug("Formulas")
        logging.debug(s)
        if res == sat:
            logging.debug("Model")
            logging.debug(s.model())
        return (is_sat, model)
