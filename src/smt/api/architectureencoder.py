'''
Created on 15.03.2014

@author: simon
'''
from functools import reduce
import logging

from z3 import Function, BoolSort, BitVecSort, ForAll, BitVecs, BitVecVal, \
    Implies, And, Const, Exists, BitVec, Not

from architecture.guarded_system import DisjunctiveGuardedArchitecture, \
    ConjunctiveGuardedArchitecture, GuardedArchitecture


class ArchitectureEncoder(object):
    '''
    Contains functionality to add architecture specific formulae
    to the SMT context
    '''

    def __init__(self, encoder_info, architecture):
        '''
        Constructor
        '''
        self._encoder_info = encoder_info
        self._architecture = architecture

    def define_eval_guard(self):
        '''
        Defines the guard evaluation function for disjunctive and
        conjunctive guarded systems
        '''
        self._encoder_info.eval_guard = \
            Function('eval_guard',
                     BitVecSort(self._encoder_info.guard_size),
                     BitVecSort(self._encoder_info.guard_size),
                     BoolSort())

        state_set, guard = BitVecs('state_set guard',
                                   self._encoder_info.guard_size)

        if isinstance(self._architecture, DisjunctiveGuardedArchitecture):
            self._encoder_info.solver.add(
                ForAll([state_set, guard],
                       self._encoder_info.eval_guard(state_set, guard) ==
                       ((state_set & guard) !=
                        BitVecVal(0, self._encoder_info.guard_size))))

        elif isinstance(self._architecture, ConjunctiveGuardedArchitecture):
            self._encoder_info.solver.add(
                ForAll([state_set, guard],
                       self._encoder_info.eval_guard(state_set, guard) ==
                       And(guard != BitVecVal(0, self._encoder_info.guard_size),
                           ((state_set | guard) == guard))))

    def add_guard_constraints(self):
        '''
        Adds architecture specific guard constraints for each template

        * system must be non-input-blocking
        * determinism regarding (current state, inputs, guard set)
        * conjunctive guards must include all templates' initial states
        * conjunctive guarded initializable systems must have an unguarded
        transition from each state to the initial state
        '''
        if isinstance(self._architecture, GuardedArchitecture):
            for template_function in self._encoder_info.template_functions:
                guard_params = template_function.get_fresh_guard_params_variables()
                other_input_params = template_function.get_fresh_input_variables(prefix="other")
                other_successor_state = Const('tnpr', template_function.state_sort)

                # if there exists a guarded transition for one input,
                # there must be a transition for all inputs
                # labeled with the same guard.
                if len(other_input_params) > 0:
                    other_guard_params = \
                        [guard_params[0]] + \
                        other_input_params + \
                        [other_successor_state]

                    constraint = \
                        ForAll(
                            guard_params,
                            Implies(template_function.guard_function(guard_params) !=
                                    BitVecVal(0, self._encoder_info.guard_size),
                                    ForAll(
                                        other_input_params,
                                        Exists(
                                            [other_successor_state],
                                            template_function.guard_function(other_guard_params) ==
                                            template_function.guard_function(guard_params)))))

                    self._encoder_info.solver.add(constraint)


                # ensure determinism regarding (current state, inputs, guard set)
                guard_parameters = template_function.get_fresh_guard_params_variables()[:-1]
                global_state_parameter = BitVec('gs', self._encoder_info.guard_size)

                successor_state_1 = Const('t_next1', template_function.state_sort)
                successor_state_2 = Const('t_next2', template_function.state_sort)

                function_parameters_1 = \
                    guard_parameters + \
                    [successor_state_1, global_state_parameter]

                function_parameters_2 = \
                    guard_parameters + \
                    [successor_state_2, global_state_parameter]

                forall_parameters = \
                    guard_parameters + \
                    [successor_state_1,
                     successor_state_2,
                     global_state_parameter]

                # there is only one enabled transition for a given tuple (current state, inputs, guard set)
                constraint = ForAll(
                    forall_parameters,
                    Implies(
                        And(template_function.is_enabled(function_parameters_1),
                            successor_state_1 != successor_state_2),
                        Not(template_function.is_enabled(function_parameters_2))))

                self._encoder_info.solver.add(constraint)

            if isinstance(self._architecture, ConjunctiveGuardedArchitecture):
                initial_bv_list = \
                    [template_function.state_guard(initial_state)
                     for template_function in self._encoder_info.template_functions
                     for initial_state in template_function.get_initial_states()]
                initial_bv = reduce(lambda x, y: x | y, initial_bv_list)

                for template_function in self._encoder_info.template_functions:
                    guard_params = template_function.get_fresh_guard_params_variables()

                    # each non-empty guard set must contain the initial states of all templates
                    constraint = \
                        ForAll(
                            guard_params,
                            Implies(
                                (template_function.guard_function(guard_params) !=
                                 BitVecVal(0, self._encoder_info.guard_size)),
                                (template_function.guard_function(guard_params) &
                                 initial_bv == initial_bv)))
                    self._encoder_info.solver.add(constraint)

        logging.debug("Solver satisfiability after adding "
                      "architecture constraints: %s",
                      str(self._encoder_info.solver.check()))
