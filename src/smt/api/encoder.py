'''
Created on 28.02.2014

@author: simon
'''
import logging
from itertools import product

from abc import abstractmethod, ABCMeta  # pylint: disable=unused-import
from z3 import Datatype, Bool, Function, BoolSort, BitVecSort, \
    ForAll, And, IntSort, Const, Or, Exists, Implies, \
    Not, UGE, UGT, Tactic, Then

from helpers.rejecting_states_finder import build_state_to_rejecting_scc
from smt.api.architectureencoder import ArchitectureEncoder
from smt.encoder_base import SMTEncoder, EncodingOptimization


class PyZ3EncoderInfo:
    '''
    Encapsulates data that is used by synthesis encoder and template encoders
    '''
    def __init__(self):
        self.solver = None
        self.is_scheduled = None
        self.eval_guard = None
        self.sched_size = None
        self.architecture_encoder = None
        self.template_functions = None
        self.spec = None


class PyZ3Encoder(SMTEncoder, metaclass=ABCMeta):
    '''
    Encodes the bounded synthesis problem using the Python Z3 API
    '''
    def __init__(self, spec, architecture,
                 encoding_optimization=EncodingOptimization.NONE):
        super(PyZ3Encoder, self).__init__(spec, architecture,
                                          encoding_optimization)
        self.encoder_info = None

    @classmethod
    def get_encoder_type(cls):
        '''
        Returns the encoder type
        '''
        return None

    def encode(self):
        '''
        Adds architectural and template specific constraints to the SMT problem
        '''
        self.encoder_info = PyZ3EncoderInfo()
        self.encoder_info.solver = Then(Tactic("qe"), Tactic("smt")).solver()

        self.encoder_info.sched_size = self.spec.get_scheduling_size()
        self.encoder_info.spec = self.spec
        self.encoder_info.architecture_encoder = \
                ArchitectureEncoder(self.encoder_info, self.architecture)

        self._init_guard_size()

        # define common functions
        self._define_eval_guard()
        self._define_is_scheduled()

        self._encode_template_functions()

        for templ_func in self.encoder_info.template_functions:
            templ_func.define_guard_set()

        self.encoder_info.architecture_encoder.add_guard_constraints()

    def _define_eval_guard(self):
        """Defines the function eval_guard: BitVec x BitVec -> Bool

        Function arguments:

        * s_s -- current global state set
        * s_g -- guard set
        """
        self.encoder_info.architecture_encoder.define_eval_guard()

    def _define_is_scheduled(self):
        """Defines the function is_scheduled: Int x Int x Sched -> Bool

        Function arguments:

        * k -- Template index
        * i -- Instance index
        * Sched -- Scheduling variables
        """
        is_scheduled_arguments = \
            [IntSort()] * 2 + \
            [BoolSort()] * self.encoder_info.sched_size + \
            [BoolSort()]
        self.encoder_info.is_scheduled = Function('is_scheduled',
                                                  is_scheduled_arguments)

        forall_params = self.get_fresh_scheduling_variables()

        for sched_value_tuple in self.spec.get_schedule_values():
            (template_index, instance_index), binval = sched_value_tuple
            compare_expr = \
                And([forall_params[bit_index]
                     if binval[bit_index]
                     else Not(forall_params[bit_index])
                     for bit_index in range(0, len(binval))])
            self.encoder_info.solver.add(
                ForAll(forall_params,
                       self.encoder_info.is_scheduled(
                           [template_index, instance_index] + forall_params) ==
                       compare_expr))

    def get_fresh_scheduling_variables(self):
        '''
        Returns fresh SMT constants that represent the current scheduling
        '''
        return [Bool('sched_%d' % i)
                for i in reversed(range(0, self.encoder_info.sched_size))]

    def get_fresh_global_state_tuples(self, cutoff=None,
                                      absent_process=(None, None)):
        '''
        Returns a list that contains one local state constant
        for each process in the system as a component of a tuple
        (state sort, template index, instance index)

        :param cutoff: Number of process instances for each template
        :param absent_process: Process for which there should not be added
                               a local state constant
        '''
        indices = self.get_process_indices(cutoff, absent_process)

        tuples = [(self.encoder_info.template_functions[k].state_sort, k, i)
                  for k, i in indices]
        return tuples

    def get_process_indices(self, cutoff=None, absent_process=(None, None)):
        '''
        Returns a list of tuples (k,i) which serve as identifier of the
        different process indices

        :param cutoff: Number of process instances for each template
        :param absent_process: Process whose identifier should not be present
                               in the resulting list
        '''
        if cutoff is None:
            cutoff = list(self.spec.cutoff)

        absent_k, absent_i = absent_process
        tuples = [(k, i) if (k, i) != (absent_k, absent_i) else None
                  for k in range(0, len(cutoff)) for i in range(0, cutoff[k])]
        if absent_k is not None and absent_i is not None \
                and tuples.__contains__(None):
            tuples.remove(None)

        return tuples

    def get_fresh_global_state_sorts(self, absent_process=(None, None),
                                     cutoff=None):
        '''
        Returns the sort components of the tuple list created by
        :meth:`get_fresh_global_state_tuples`

        :param absent_process:
            Process for which there should not be added a local state sort
        :param cutoff: System size
        '''
        return [t[0] for t in
                self.get_fresh_global_state_tuples(cutoff, absent_process)]

    def get_fresh_global_state_variables(self, cutoff=None,
                                         absent_process=(None, None),
                                         prefix=None, include_indices=False):
        '''
        Returns a list of local state constants such that the constant
        sorts match the sort components of the tuple list created by
        :meth:`get_fresh_global_state_tuples`

        The constant names are t_k_i, where k is the

        :param cutoff: System size
        :param absent_process:
            Process for which there should not
            be created a local state variable
        :param prefix: Prefix which should be contained in the constants' names
        '''
        template_index, instance_index = absent_process
        if template_index is not None:
            assert instance_index is not None

        prefix = "" if prefix is None else prefix + '_'

        res = [((t[1], t[2]),
                Const('t_%s%d_%d' % (prefix, t[1], t[2]), t[0]))
               for t in self.get_fresh_global_state_tuples(cutoff,
                                                           absent_process)]

        return res if include_indices else [var for k_i, var in res]

    def _get_initial_system_states(self, cutoff=None):
        """
        Returns all possible combinations of local initial states
        """
        templates_instance_index_tuples = \
            self._get_templates_instance_index_tuples(cutoff)

        initial_state_sets_list = \
            [template_inst_index_tuple[0].get_initial_states()
             for template_inst_index_tuple in templates_instance_index_tuples]

        return product(*initial_state_sets_list)

    def _get_templates_instance_index_tuples(self, cutoff=None):
        """
        Returns a list of tuples (template_function_0, 0)
        (template_function_0, 1) ... (template_function_k, n_k) for each
        template and instance
        """
        if cutoff is None:
            cutoff = self.spec.cutoff
        assert(len(cutoff) == len(self.spec.cutoff))

        return [(self.encoder_info.template_functions[k], i)
                for k in range(0, len(cutoff)) for i in range(0, cutoff[k])]

    def _compare_scheduling(self, transition_label, current_scheduling):
        '''
        Checks whether a given UCT transition label dictionary is such that it
        either contains no information about schedulings or matches the current
        scheduling

        :param transition_label: transition label assignments
        :param current_scheduling: current scheduling variable assignments
        '''
        for item in current_scheduling.items():
            if (transition_label.__contains__(item[0])) and \
                    transition_label[item[0]] != item[1]:
                return False
        return True

    def get_relative_global_state(self, global_state_tuples,
                                  template_index, instance_index,
                                  include_tuples=False):
        '''
        Returns the relative global state (relative means global state from a
        particular process' perspective, i.e., the global state without this
        process' local state)

        The relative global state is equal to the given global state without
        the state tuple that corresponds to the given process identified by
        (template_index, instance_index).

        If the parameter include_tuples is false, only the state constants are
        returned, otherwise the process identifying tuple (k,i) is included.

        :param global_state_tuples: List of tuples ((k, i), constant)
        :param template_index: template index of the particular process
        :param instance_index: instance index of the particular process
        :param include_tuples: Determines whether process identifying tuples
                               (k,i) should be included in the result set
        '''
        filtered_global_state_tuples = \
            [(k_i, state_variable) for k_i, state_variable in
             [k_i_state_tuple for k_i_state_tuple in global_state_tuples
              if k_i_state_tuple[0] != (template_index, instance_index)]]

        if include_tuples:
            return filtered_global_state_tuples
        else:
            return [state for _, state in filtered_global_state_tuples]

    def _avoid_deadlocks(self, uct_sort, lambda_b_function,
                         cutoff, global_cutoff):
        '''
        Adds formula that ensures that for each global state s for which
        :math:`lambda^B(q, s)` is true, there exists at least one enabled local
        transition (i.e., there exists an input s.t. one transition is enabled)

        :param uct_sort: UCT state sort
        :param lambda_b_function: lambda^B function
        :param cutoff: cut-off for the currently encoded automaton
        :param global_cutoff: overall maximum system size
        '''
        uct_state = Const('q', uct_sort)
        global_state_tuples = \
            self.get_fresh_global_state_variables(cutoff=cutoff,
                                                  prefix="curr",
                                                  include_indices=True)
        global_state_dict = dict(global_state_tuples)
        global_state = [t for _, t in global_state_tuples]

        cutoff_global_state_indices = \
            [k_i for k_i, _ in self.get_fresh_global_state_variables(
                cutoff=global_cutoff, include_indices=True)]

        composition_state = [uct_state] + global_state

        def build_enabled_call(self, k, i):
            templ_func = self.encoder_info.template_functions[k]
            others_global_state = \
                self.get_relative_global_state(global_state_tuples, k, i, True)

            inputs = templ_func.get_fresh_input_variables()
            gs = templ_func.guard_set(
                self._blowup_state_set(others_global_state,
                                       cutoff_global_state_indices, (k, i)))

            params = [global_state_dict[(k, i)]] + inputs + [gs]
            constraint = \
                self.encoder_info.template_functions[k].is_any_enabled(params)
            return Exists(inputs, constraint) if len(inputs) else constraint

        enabled_expressions = [build_enabled_call(self, k, i)
                               for (k, i), t in global_state_tuples]

        # pylint: disable=star-args
        constraint = ForAll(composition_state,
                            Implies(lambda_b_function(composition_state),
                                    Or(*enabled_expressions)))
        self.encoder_info.solver.add(constraint)

    def encode_automata(self, automata_infos, global_cutoff):
        for automaton, automaton_index, is_architecture_specific, cutoff \
                in automata_infos:
            self.encode_automaton(automaton, automaton_index,
                                  is_architecture_specific, cutoff,
                                  global_cutoff)

    def encode_automaton(self, automaton, automaton_index,
                         is_architecture_specific, cutoff, global_cutoff):
        '''
        Encodes the given automaton

        :param automaton: Automaton instance
        :param automaton_index: Automaton index used for identifying the lambda
                                function corresponding to the automaton
        :param is_architecture_specific: Whether automaton is required
                                         by the used architecture
        :param cutoff: Cut-off associated with the current automaton
        :param global_cutoff: Maximum of all automata-specific cut-offs
        '''
        # declare UCT state
        uct_state = Datatype('Q_%d' % automaton_index)
        state_prefix = 'q%d_' % automaton_index

        nodes_list = list(automaton.nodes)
        for node in nodes_list:
            uct_state.declare(state_prefix + node.name)
        uct_state = uct_state.create()
        uct_states_dict = {nodes_list[i].name:
                           getattr(uct_state, uct_state.constructor(i).name())
                           for i in range(len(nodes_list))}

        # declare lambda functions
        lambda_b_function_argument_sorts = \
            [uct_state] + \
            self.get_fresh_global_state_sorts(cutoff=cutoff) + \
            [BoolSort()]

        lambda_b_function = Function('lambda_b_%d' % (automaton_index),
                                     lambda_b_function_argument_sorts)

        lambda_s_function_argument_sorts = \
            [uct_state] + \
            self.get_fresh_global_state_sorts(cutoff=cutoff) + \
            [IntSort()]

        lambda_s_function = Function('lambda_s_%d' % (automaton_index),
                                     lambda_s_function_argument_sorts)

        # avoid global deadlocks in case of the fairness property
        if is_architecture_specific:
            self._avoid_deadlocks(uct_state, lambda_b_function,
                                  cutoff, global_cutoff)

        assert(len(automaton.initial_sets_list) == 1)
        initial_uct_states = [uct_states_dict[node.name]
                              for node in automaton.initial_sets_list[0]]
        initial_system_states = self._get_initial_system_states(cutoff=cutoff)

        # list of tuples in format (q0, (t1, t2, ...))
        initial_state_tuples = product(*[initial_uct_states,
                                         initial_system_states])
        # merge tuples
        initial_state_tuples = [tuple([item[0]] + list(item[1]))
                                for item in initial_state_tuples]

        logging.debug("Automaton %d   Initial states: %s",
                      automaton_index, initial_state_tuples)

        for initial_uct_state in initial_state_tuples:
            self.encoder_info.solver.add(lambda_b_function(initial_uct_state))
            self.encoder_info.solver.add(lambda_s_function(initial_uct_state) == 0)

        # (template function, instance index)
        template_instance_index_tuples = \
            self._get_templates_instance_index_tuples(cutoff=cutoff)

        # assignment of the scheduling variables the particular processes
        # are scheduled (k,i) -> scheduling variable assignment list
        schedule_values_dict = dict(self.spec.get_schedule_values())
        scheduling_signals = self.spec.get_scheduling_signals()

        # used for SCC lambda_s optimization
        sccs = build_state_to_rejecting_scc(automaton)
        scc_lambda_functions = \
            {scc: Function('lambda_s_%d_%d' % (automaton_index, scc_index),
                           [uct_state] +
                           self.get_fresh_global_state_sorts(cutoff=cutoff) +
                           [BitVecSort(len(scc))])
             for scc_index, scc in enumerate(sccs.values())}

        spec_cutoff_process_indices = \
            self.get_process_indices(cutoff=self.spec.cutoff)

        global_state_tuples = \
            self.get_fresh_global_state_variables(cutoff=cutoff,
                                                  prefix="curr",
                                                  include_indices=True)

        global_state_dict = dict(global_state_tuples)

        current_global_state = [state_variable for _, state_variable
                                in global_state_tuples]

        input_signals_set = {(t[0].template_index, t[1]):
                             t[0].get_input_signals(t[1])
                             for t in template_instance_index_tuples}

        input_signals_list = [sig for t in template_instance_index_tuples
                              for sig in t[0].get_input_signals(t[1])]

        input_signal_expr_dict = {sig: Bool(str(sig))
                                  for sig in input_signals_list}

        # dictionary of output signals -> function call
        output_signal_expr_dict = \
            {signal_name:
             signal_function(global_state_dict[(template_function.template_index,
                                                instance_index)])
             for template_function, instance_index in template_instance_index_tuples
             for signal_name, signal_function in
             template_function.get_output_signals_function_dict(instance_index).items()}

        function_placeholder_signals_set = \
             set(self.architecture.get_placeholder_signals(cutoff))

        transitions = [(src_node, transition, target_node_info)
                       for src_node in automaton.nodes
                       for transition, target_node_infos
                       in src_node.transitions.items()
                       for target_node_info in target_node_infos[0]]
        node = None
        for src_node, transition, target_node_info in transitions:

            target_node, is_rejecting_target_node = target_node_info

            logging.debug("Automaton: %d: %s->%s, condition: %s",
                          automaton_index, src_node.name, target_node.name,
                          transition)

            for templ_func, i in template_instance_index_tuples:
                # we use k for the template index and i for the instance index
                # as defined in the paper
                k = templ_func.template_index

                others_global_state_tuples = \
                    [(k_i, state_variable)
                     for k_i, state_variable in
                     filter(lambda k_i_state_tuple: k_i_state_tuple[0] !=
                            (k, i),
                            global_state_tuples)]

                others_global_state = [state for _, state
                                       in others_global_state_tuples]

                current_local_state = global_state_dict[(k, i)]

                next_local_state = Const('t_next_%d_%d' % (k, i),
                                         templ_func.state_sort)
                next_global_state = [state
                                     if k_i != (k, i)
                                     else next_local_state
                                     for k_i, state in global_state_tuples]

                # get scheduling assignment if current instance is scheduled
                sched_assignment = schedule_values_dict[(k, i)]
                sched_assignment_dict = \
                    {scheduling_signals[i]: sched_assignment[i]
                     for i in range(0, len(scheduling_signals))}

                logging.debug("\tinstance: (%d, %d) sched=%s",
                              k, i, sched_assignment)

                # parameters for functions
                guard_set_call_expr = \
                    templ_func.guard_set(
                        self._blowup_state_set(others_global_state_tuples,
                                               spec_cutoff_process_indices,
                                               (k, i)))

                # only add constraint if scheduling assignment
                # matches the label
                if not self._compare_scheduling(sched_assignment_dict,
                                                transition):
                    logging.debug("\tSKIP %s->%s, condition: %s, scheduling=%s"
                                  % (src_node.name, target_node.name,
                                     transition, sched_assignment))
                    continue

                transition_keys = set(transition.keys())
                used_input_signals = transition_keys.intersection(set(input_signals_list))
                used_output_signals = transition_keys.intersection(output_signal_expr_dict.keys())
                used_placeholder_signals = transition_keys.intersection(function_placeholder_signals_set)
                used_scheduler_signals = transition_keys.intersection(set(scheduling_signals))

                assert(len(used_input_signals) + \
                       len(used_output_signals) + \
                       len(used_placeholder_signals) + \
                       len(used_scheduler_signals) == len(transition.items()))

                condition = []

                for input_signal in used_input_signals:
                    condition.append(input_signal_expr_dict[input_signal] ==
                                     transition[input_signal])

                for output_signal in used_output_signals:
                    condition.append(output_signal_expr_dict[output_signal] ==
                                     transition[output_signal])

                for placeholder_signal in used_placeholder_signals:
                    ph_instance = (placeholder_signal.template_index,
                                   placeholder_signal.instance_index)
                    ph_relative_global_state_tuples = \
                        list(filter(lambda x: x[0] !=
                                    ph_instance, global_state_tuples))
                    ph_template_func = self.encoder_info.template_functions[
                        placeholder_signal.template_index]

                    ph_gs = ph_template_func.guard_set(
                        self._blowup_state_set(ph_relative_global_state_tuples,
                                               spec_cutoff_process_indices,
                                               ph_instance))

                    ph_relative_current_local_state = global_state_dict[ph_instance]
                    ph_relative_current_inputs = \
                        [input_signal_expr_dict[sig]
                         for sig in input_signals_set[ph_instance]]

                    if placeholder_signal.name.startswith('enabled'):
                        condition.append(ph_template_func.is_any_enabled(
                            [ph_relative_current_local_state] + \
                            ph_relative_current_inputs + \
                            [ph_gs]) == transition[placeholder_signal])
                    elif placeholder_signal.name.startswith('active'):
                        condition.append(self.encoder_info.is_scheduled(
                            [placeholder_signal.template_index,
                             placeholder_signal.instance_index] + \
                            sched_assignment) == transition[placeholder_signal])
                    elif placeholder_signal.name.startswith('init'):
                        req_initial_states = ph_template_func.get_initial_states()
                        assert(len(req_initial_states) == 1)
                        condition.append(
                            (ph_relative_current_local_state == req_initial_states[0]) ==
                            transition[placeholder_signal])
                    else:
                        raise Exception(placeholder_signal.name)

                condition_expression = True
                if len(condition) > 0:
                    condition_expression = And(*condition)

                current_local_input_arguments = [input_signal_expr_dict[sig]
                                                 for sig in input_signals_set[(k, i)]]
                input_arguments = [input_signal_expr_dict[signal]
                                   for signal in input_signals_list]
                forall_arguments = \
                    [current_local_state, next_local_state] + \
                    others_global_state + \
                    input_arguments

                current_combined_state_parameters = \
                    [uct_states_dict[src_node.name]] + \
                    current_global_state
                next_combined_state_parameters = \
                    [uct_states_dict[target_node.name]] + \
                    next_global_state

                delta_enabled_function_parameters = [current_local_state] + \
                                                    current_local_input_arguments + \
                                                    [next_local_state] + \
                                                    [guard_set_call_expr]

                lambda_s_req_expr = None
                if self._encoding_optimization & EncodingOptimization.LAMBDA_SCC:
                    logging.debug("Use LAMBDA_SCC optimization")
                    lambda_s_req_expr = True
                    current_scc = sccs.get(src_node)
                    if current_scc is not None and current_scc == sccs.get(target_node):
                        scc_ls_func = scc_lambda_functions[current_scc]
                        lambda_s_req_expr = \
                            [UGE, UGT][is_rejecting_target_node](scc_ls_func(next_combined_state_parameters),
                                                                 scc_ls_func(current_combined_state_parameters))
                else:
                    # using no lambda_s optimizations
                    if is_rejecting_target_node:
                        lambda_s_req_expr = (
                            lambda_s_function(next_combined_state_parameters) >
                            lambda_s_function(current_combined_state_parameters))
                    else:
                        lambda_s_req_expr = (
                            lambda_s_function(next_combined_state_parameters) >=
                            lambda_s_function(current_combined_state_parameters))

                extended_condition_expr = \
                    templ_func.delta_enabled_functions[i](
                        delta_enabled_function_parameters)

                extended_condition_expr = \
                    Or(extended_condition_expr,
                       And(current_local_state == next_local_state,
                           Not(templ_func.is_any_enabled(
                               [current_local_state] + \
                               current_local_input_arguments + \
                               [guard_set_call_expr]))))

                expr = ForAll(forall_arguments, Implies(
                    And(lambda_b_function(current_combined_state_parameters),
                        condition_expression,
                        extended_condition_expr),
                    And(lambda_b_function(next_combined_state_parameters),
                        lambda_s_req_expr)))

                logging.debug("\tADD  %s->%s, condition: %s, scheduling=%s",
                              src_node.name, target_node.name,
                              transition, sched_assignment)

                self.encoder_info.solver.add(expr)

    def _blowup_state_set(self, others_global_state_tuples,
                          global_state_tuples, absent_template_index=None):
        '''
        Duplicates states contained in other_global_state_tuples, such that the
        size of the current global state is equal to the global state under
        consideration of the global cut-off.

        This functionality is needed to generate parameters for functions that
        expect the global state. These functions only exist once in the SMT
        instance and consider a global state whose size is as defined
        by the global cut-off.

        The resulting global state list has the size as defined by the global
        cut-off, or 1 less in case there is a process which should not be
        contained (identified by absent_template_index)

        :param others_global_state_tuples: Global state tuples ((k, i),
            state constant)
        :param global_state_tuples: Global state tuples as defined by the
            global cut-off
        :param absent_template_index: identifier for the process which is
            missing in the others_global_state_tuples parameter
        '''
        template_repr_state_dict = {k: state for (k, i), state in
                                    others_global_state_tuples}
        others_global_state_dict = dict(others_global_state_tuples)

        res = [None] * len(global_state_tuples)
        for index, (k, i) in enumerate(global_state_tuples):
            if(k, i) != absent_template_index:
                res[index] = others_global_state_dict[(k, i)] \
                    if others_global_state_dict.__contains__((k, i)) \
                    else template_repr_state_dict[k]
        res = [x for x in res if x is not None]
        return res

    @abstractmethod
    def _init_guard_size(self):
        '''
        Initializes the :attr:`encoder_info.guard_size` variable
        '''
        pass

    @abstractmethod
    def _encode_template_functions(self):
        '''
        Creates required :class:`TemplateFunction` instances and
        stores them into :attr:`self.encoder_info.template_functions

        :note: This method is abstract because the concrete
               :class:`TemplateFunction`class depends on the particular
               encoding.
        '''
        pass
