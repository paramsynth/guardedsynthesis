import logging

from abc import abstractmethod, ABCMeta
from functools import reduce

from z3 import BoolSort, Bool, Datatype, Function, BitVecSort, BitVec, \
    BitVecVal, Const, ForAll, Exists, IntSort, And, Int, Implies, Or


class TemplateFunction(metaclass=ABCMeta):
    '''
    Provides functionality for generating and adding template
    specific formulae to the SMT context
    '''

    def __init__(self, template, encoder, encoder_info, spec):
        self._template = template
        self._spec = spec
        self._encoder = encoder
        self._encoder_info = encoder_info

        # state
        self.state_type = Datatype('T%d' % template.template_index)
        for i in range(0, template.bound):
            self.state_type.declare('t%d_%d' % (template.template_index, i))
        self.state_sort = self.state_type.create()

        # output functions
        self.output_functions = [Function(str(output_signal),
                                          self.state_sort, BoolSort())
                                 for output_signal in template.outputs]

        logging.debug("Output functions for template %d: %s",
                      template.template_index, self.output_functions)

        self.guard_function = None
        # guard function: t, I, t' -> g [BitVec(Sum_i |Ti|])
        self._define_guard()

        # transition enabled
        self.is_enabled = None
        self._define_is_enabled()

        # any enabled
        self.is_any_enabled = None
        self._define_is_any_enabled()

        # lazy initialization
        self._guard_set = None

        self.state_guard = None
        self._define_state_guard()

        # declare function
        self.delta_enabled_functions = [self._get_delta_enabled_function(i)
                                        for i in range(0, template.cutoff)]

#         self._define_optimizations()

    def _define_guard(self):
        """Defines the guard function

        guard: T, I, T -> BitVec(Sum_i |Ti|)
        t  -- current state
        i  -- multiple parameters corresponding to the inputs I
        t' -- successor state
        """

        guard_function_params = [self.state_sort] + \
            self._get_input_sorts() + \
            [self.state_sort] + \
            [BitVecSort(self._encoder_info.guard_size)]
        self.guard_function = Function(str('guard_%d' %
                                           self._template.template_index),
                                       guard_function_params)

    def _get_delta_enabled_function(self, instance_index):
        """Defines the function delta_enabled

        delta_enabled_i: T x I x T x S' -> Bool
        t, i, t -- transition identifying values
        s_s     -- current global state set

        The scheduling must be ensured by an external function.

        """
        function_arguments = self._get_guard_params_sorts() + \
            [BitVecSort(self._encoder_info.guard_size)] + [BoolSort()]

        function_declaration = Function('delta_enabled_%d_%d' %
                                        (self._template.template_index,
                                         instance_index),
                                        function_arguments)

        t_current_variable = Const('tc', self.state_sort)
        t_next_variable = Const('tn', self.state_sort)
        input_variables = \
            self._get_fresh_input_variables(instance_index=instance_index)
        guard_params = [t_current_variable] + \
            input_variables + \
            [t_next_variable]

        current_guard_set_parameter = BitVec('s', self._encoder_info.guard_size)

        function_parameters = guard_params + [current_guard_set_parameter]

        function_body = \
            ForAll(function_parameters,
                   function_declaration(function_parameters) ==
                   self._encoder_info.eval_guard(current_guard_set_parameter,
                                                 self.guard_function(guard_params)))

        self._encoder_info.solver.add(function_body)
        return function_declaration

    def _define_is_any_enabled(self):
        """Defines the function is_any_enabled

        is_any_enabled checks if there exists at least one enabled
        transition for a given

        * current state
        * input values
        * global state set

        is_any_enabled: T x I x S' -> Bool
        t, i -- part of transition identifying values
        s_s  -- global state set
        """
        function_arguments = self._get_guard_params_sorts()[:-1] + \
            [BitVecSort(self._encoder_info.guard_size), BoolSort()]

        # function declaration
        self.is_any_enabled = Function('is_any_enabled_%d' %
                                       (self._template.template_index),
                                       function_arguments)

        # function body
        guard_parameters = self.get_fresh_guard_params_variables()[:-1]
        global_state_parameter = BitVec('gs', self._encoder_info.guard_size)
        function_parameters = guard_parameters + [global_state_parameter]

        t_next = Const('tn', self.state_sort)

        function_body = \
            ForAll(function_parameters,
                   self.is_any_enabled(function_parameters) ==
                   Exists(t_next,
                          self._encoder_info.eval_guard(
                              global_state_parameter,
                              self.guard_function(guard_parameters + [t_next]))))
        self._encoder_info.solver.add(function_body)

    def _define_is_enabled(self):
        '''
        Defines the function is_enabled

        is_enabled checks if the transition identified by
        (current state, next state) is enabled for the given

        * input values
        * global state set

        is_any_enabled: T x I x T x S' -> Bool
        t, i, t -- current state, input, next state
        s_s     -- global state set
        '''

        function_arguments = \
            self._get_guard_params_sorts() + \
            [BitVecSort(self._encoder_info.guard_size), BoolSort()]

        # function declaration
        self.is_enabled = Function('is_enabled_%d' %
                                   (self._template.template_index),
                                   function_arguments)

        # function body
        guard_parameters = self.get_fresh_guard_params_variables()
        global_state_parameter = BitVec('gs', self._encoder_info.guard_size)
        function_parameters = guard_parameters + [global_state_parameter]

        function_body = \
            ForAll(function_parameters,
                   self.is_enabled(function_parameters) ==
                   self._encoder_info.eval_guard(
                       global_state_parameter,
                       self.guard_function(guard_parameters)))

        self._encoder_info.solver.add(function_body)

    @property
    def guard_set(self):
        '''
        Guard set function
        '''
        if self._guard_set is None:
            self.define_guard_set()
        return self._guard_set

    def define_guard_set(self):
        """
        Defines the method that determines the relative global states guard set

        T1 T1 ... T1 T2 ... Tn -> BitVec
        """
        function_arguments = \
            self._encoder.get_fresh_global_state_sorts(
                absent_process=(self._template.template_index, 0)) + \
            [BitVecSort(self._encoder_info.guard_size)]
        function_declaration = Function('guard_set_%d' %
                                        (self._template.template_index),
                                        function_arguments)

        self._guard_set = function_declaration

        # function body
        global_state_tuples_parameters = \
            self._encoder.get_fresh_global_state_variables(
                absent_process=(self._template.template_index, 0))

        global_state_tuples_indices = \
            [k for _, k, _ in
             self._encoder.get_fresh_global_state_tuples(
                 absent_process=(self._template.template_index, 0))]
        function_parameters = global_state_tuples_parameters

        assert(len(global_state_tuples_parameters) ==
               len(global_state_tuples_indices))

        bit_sum_expr = \
            reduce(lambda x, y: x | y,
                   [self._encoder_info.template_functions
                    [global_state_tuples_indices[i]].state_guard(
                        global_state_tuples_parameters[i])
                    for i in range(0, len(global_state_tuples_indices))])

        function_body = ForAll(function_parameters,
                               function_declaration(function_parameters) ==
                               bit_sum_expr)
        self._encoder_info.solver.add(function_body)

    def _get_guard_params_sorts(self):
        '''
        Returns the guard parameter sorts T_k x I_k x T_k
        where I_k is Bool x Bool x ... x Bool (depending on number of inputs)
        '''
        return [self.state_sort] + self._get_input_sorts() + [self.state_sort]

    def get_fresh_guard_params_variables(self):
        '''
        Returns new guard parameter variables (tc, i_k, tn) of T_k x I_k x T_k

        The variable names are tc, tn, and inputs as defined by the signal names
        '''
        return [Const('tc', self.state_sort)] + \
                self._get_fresh_input_variables() + \
                [Const('tn', self.state_sort)]

    def _get_fresh_input_variables(self, instance_index=None, sfx_pfx=""):
        '''
        Gets fresh input variables i_k of I_k (i.e., Boolean variables of Boolean)

        The signal name can be extended by a suffix that consists of the
        parameter sfx_pfx concatenated with an optional instance index.
        By default, the variable name is equal to the signal name.

        :param instance_index:
        :param sfx_pfx:
        '''
        suffix = sfx_pfx or "" + ("" if instance_index is None \
                                  else "_" + str(instance_index))

        return [Bool(str(input_signal) + suffix)
                for input_signal in self._template.inputs]

    def get_fresh_input_variables(self, prefix=None):
        '''
        Returns fresh input variables

        :todo: TODO: clear, improve!
               instance_index can also be some suffix string
        :param prefix:
        '''
        return self._get_fresh_input_variables(instance_index=prefix)

    def get_fresh_input_assignments(self):
        '''
        Returns a tuple of possible assignments for each input variable
        '''
        return [(False, True)] * len(self._template.inputs)

    def _get_input_sorts(self):
        '''
        Returns a list of sorts used for the SMT representation of the
        template's input signals
        '''
        return [BoolSort(), ] * len(self._template.inputs)

    def get_initial_states(self):
        '''
        Returns Z3 consts that represent initial states of the given template
        '''
        return [getattr(self.state_sort, self.state_sort.constructor(i).name())
                for i in range(len(self._template.initial_states))]

    def get_input_signals(self, instance_index=None):
        '''
        Returns input signals for a particular instance or quantified signals

        Returns the input signals for a single instance of the particular
        template or the quantified template signals if no instance index is
        provided

        :param instance_index:
        '''
        if instance_index is None:
            return self._template.inputs
        return [template_input.get_instance_signal(instance_index)
                for template_input in self._template.inputs]

    def get_output_signals_function_dict(self, instance_index):
        """
        Returns output signal mapped to SMT functions

        Returns a dictionary of signal name -> SMT function for all
        instantiated signal names corresponding to template signals
        """
        return {self._template.outputs[i].get_instance_signal(instance_index):
                self.output_functions[i] for i
                in range(0, len(self.output_functions))}

    def _define_optimizations(self):
        # add state order
        idx_state_func = Function('state_index%d' % self.template_index,
                                        IntSort(), self.state_sort)
        state_indices = [(getattr(self.state_sort,
                          self.state_sort.constructor(i).name()), i)
                         for i in range(0, self._template.bound)]

        state_order_conjuncts = \
            [idx_state_func(index) == state
             for state, index in state_indices]
        self._encoder_info.solver.add(And(state_order_conjuncts))

        # if t_i is connected some t_{j} with j>=i+2, then there
        # must be a connection from t_i to t_{i+1} or there is some
        # other incoming transition for the particular node
        idx_curr_var = Int('idx_curr')
        idx_next_var = Int('idx_next')
        input_vars = self.get_fresh_input_variables()

        guard_params = [idx_state_func(idx_curr_var)] + input_vars + \
            [idx_state_func(idx_next_var)]
        exists_transition2 = \
            Exists(
               input_vars + [idx_next_var],
               And(idx_next_var > idx_curr_var + 1,
                   (self.guard_function(guard_params) !=
                    BitVecVal(0, self._encoder_info.guard_size))))

        guard_params = [idx_state_func(idx_curr_var)] + input_vars + \
            [idx_state_func(idx_curr_var + 1)]
        exists_transition1 = \
            Exists(
               input_vars,
               (self.guard_function(guard_params) !=
                BitVecVal(0, self._encoder_info.guard_size)))

        input_vars_other = self.get_fresh_input_variables(prefix="other")
        idx_other_var = Int('idx_other')
        guard_params = [idx_state_func(idx_other_var)] + input_vars_other + \
            [idx_state_func(idx_curr_var + 1)]
        exists_transition1_other = \
            Exists(
               [idx_other_var] + input_vars_other,
               And(idx_other_var != idx_curr_var + 1,
                   self.guard_function(guard_params) !=
                   BitVecVal(0, self._encoder_info.guard_size)))

#         self._encoder_info.solver.add(
#             ForAll([idx_curr_var],
#                Implies(
#                    And([idx_curr_var >= 0,
#                         idx_curr_var < self._template.bound - 2]),
#                    Implies(exists_transition2,
#                            Or(exists_transition1, exists_transition1_other)))))

    @property
    def template_index(self):
        return self._template.template_index

    @abstractmethod
    def _define_state_guard(self):
        pass
