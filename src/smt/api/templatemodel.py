from itertools import product

from z3 import is_true


class ApiTemplateModel(object):
    '''
    Encapsulates information about a template model and
    provides functionality to extract this information from
    a given Z3 API model
    '''
    def __init__(self, model, template_function):
        self.states = None
        self.outputs = None
        self.transitions = None
        self.guard_state_bits = None

        self._template_function = template_function
        self.model = model

        self._internal_states = None
        self.num_guards = None

        self._init_states()
        self._init_outputs()
        self._init_transitions()

    def _init_states(self):
        '''
        Initializes the template's states (fixed by template skeleton)
        '''
        self._internal_states = \
            [getattr(self._template_function.state_sort,
                     self._template_function.state_sort.constructor(i).name())
             for i in range(
                 self._template_function.state_sort.num_constructors())]

        self.states = \
            [self._template_function.state_sort.constructor(i).name()
             for i in range(
                 self._template_function.state_sort.num_constructors())]

    def _init_outputs(self):
        '''
        Stores the output assignments from the model to :data:`outputs` member
        '''
        def _get_output_assignment(output_function):
            state_sort = self._template_function.state_sort
            return {state_name:
                    is_true(self.model.evaluate(
                        output_function(getattr(state_sort, state_name))))
                    for state_name in self.states}

        self.outputs = {str(output): _get_output_assignment(output)
                        for output in self._template_function.output_functions}

    def _init_transitions(self):
        '''
        Extracts the transitions from the Z3 model.

        The guard information is only stored numerically,
        since the other template models may not yet have been extracted.
        '''
        self.num_guards = {}

        transition_combinations = [self._internal_states] + \
            list(self._template_function.get_fresh_input_assignments()) + \
            [self._internal_states]

        transition_combinations = product(*transition_combinations)
        for transition_combination in transition_combinations:
            string_transition_combination = \
                tuple([str(transition_combination[0])] +
                      list(transition_combination[1:-1]) +
                      [str(transition_combination[-1])])
            val = self.model.evaluate(self._template_function.guard_function(
                transition_combination)).as_long()
            if val != 0:
                self.num_guards[string_transition_combination] = val

    @property
    def transitions_list(self):
        """
        Returns a list of transitions

        Transitions are triples (current state, ([(signal name, value)]*,
        guard set), successor state)
        """
        input_signals = self._template_function.get_input_signals()
        return [(t[0], (zip(input_signals, t[1:-1]), g), t[-1])
                for t, g in self.transitions.items()]

    def __repr__(self):
        return '\n'.join(
            ["\n\tTemplate %d" % self._template_function.template_index,
             "\tStates: %s" % self.states,
             # "\tGuard Bits: %s" % self._get_sorted_guard_bits_str(),
             "\tOutputs: %s" %
             self._tuples_to_str(self._get_sorted_output_str_tuples(),
                                 initial_newline=False),
             "\tTransitions: %s\n" %
             self._tuples_to_str((self.num_guards if
                                  self.transitions is None
                                  else self.transitions).items())])
    __str__ = __repr__

    def _tuples_to_str(self, value_tuples, initial_newline=True):
        return (("\n\t         " if initial_newline else "") +
                "\n\t         ".join(["%s: %s" % (str(t), str(g))
                                      for t, g in value_tuples]))

    def _get_sorted_output_str_tuples(self):
        # sort by signal name
        sorted_tuples = sorted(self.outputs.items())
        # sort state to assignment dict
        sorted_tuples = [(name, "{%s}" %
                          ", ".join(["%s: %s" % (state, assignment)
                                     for state, assignment
                                     in sorted(assignment_dict.items())]))
                         for name, assignment_dict in sorted_tuples]
        return sorted_tuples
