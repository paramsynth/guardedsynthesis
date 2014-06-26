'''
Created on 15.05.2014

@author: simon
'''
import logging

from z3 import And, BoolVal, Not, Or, sat

from smt.api.encoder import PyZ3Encoder
from smt.api.labelguarded.templatemodel import LabelGuardedTemplateModel
from smt.encoder_base import EncodingOptimization, SMTEncoder


class LabelGuardedPyZ3Encoder(PyZ3Encoder):
    def __init__(self, spec, architecture,
                 encoding_optimization=EncodingOptimization.NONE):
        super(LabelGuardedPyZ3Encoder, self).__init__(spec,
                                                      architecture,
                                                      encoding_optimization)

    @classmethod
    def get_encoder_type(cls):
        return SMTEncoder.LABEL_GUARD_ENCODER

    def _handle_result(self, solver, result):
        logging.info("Solver result: %s" % result)
        logging.debug("Formulas")
        logging.debug(solver)
        if result == sat:
            model = {}
            bits_to_states_dict = {}
            for t in self.encoder_info.template_functions:
                template_model = LabelGuardedTemplateModel(solver.model(), t)
                bits_to_states_dict.update(template_model.output_bit_state_dict)
                model[t.template_index] = template_model
                for template_model in model.values():
                    template_model.init_labeled_transitions(bits_to_states_dict)

            logging.debug("Model")
            logging.debug(solver.model())
            return model
        return None

    def check(self):
        s = self.encoder_info.solver

        aux_var_switches = [template_function.aux_label_switches
                            for template_function in
                            self.encoder_info.template_functions]

        # TODO: roundrobin etc.
        aux_switch_list = [aux_var for template_aux_vars in aux_var_switches
                        for aux_var in template_aux_vars]

        if aux_switch_list:
            for aux_index in range(len(aux_switch_list)):
                s.push()

                s.append(And([BoolVal(True)] + aux_switch_list[:aux_index]))
                s.append(Not(Or([BoolVal(False)] +
                                aux_switch_list[aux_index:])))

                res = s.check()
                model = self._handle_result(s, res)
                s.pop()
                if model is not None:
                    return (True, model)
            return (False, None)
        else:
            model = self._handle_result(s, s.check())
            return (model is not None, model)

    def _init_guard_size(self):
        self.encoder_info.guard_slice_sizes = \
            [int(2 ** (len(template.outputs)))
             # + ceil(log(template.bound, 2))))
             for template in self.spec.templates]
        self.encoder_info.guard_size = sum(self.encoder_info.guard_slice_sizes)

        logging.debug("Guard slice sizes: %s" %
                      str(self.encoder_info.guard_slice_sizes))

    def _encode_template_functions(self):
        # create templates
        from smt.api.labelguarded.templatefunction import TemplateFunction
        self.encoder_info.template_functions = \
            [TemplateFunction(template, self, self.encoder_info, self.spec)
             for template in self.spec.templates]
