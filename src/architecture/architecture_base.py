from interfaces.parser_expr import InstanceSignal


class Architecture(object):
    '''
    Base class for distributed system architectures
    '''

    def __init__(self, spec):
        self._spec = spec

    def get_architecture_assumptions(self, template_indices):
        '''
        Returns architecture-specific assumptions for
        assumption -> guarantee style properties

        :param template_indices: Tuple of template indices
        given by the specification
        '''
        pass

    def get_architecture_guarantees(self, template_indices):
        '''
        Returns architecture-specific guarantees for
        assumption -> guarantee style properties

        :param template_indices: Tuple of template indices
        given by the specification
        '''
        pass

    def get_architecture_properties(self, template_indices):
        '''
        Returns architecture-specific properties which are
        independent from other assumption -> guarantee style
        properties and thus not influenced by
        :func:`get_architecture_assumptions` and
        :func:`get_architecture_guarantees`

        :param template_indices:
        '''

        pass

    def get_placeholder_signals(self, template_instances):
        '''
        Returns a set of :class:`interfaces.parser_expr.InstanceSignal`
        instances that represent placeholders usable in the LTL specification

        :param template_instances:
        '''
        return {InstanceSignal(name, k, i)
                for k in range(0, len(template_instances))
                for i in range(0, template_instances[k])
                for name in ['enabled', 'active', 'init']}

    def determine_cutoffs(self, bound):
        '''
        Determines the cut-off for the architecture based on

        * the properties defined by the specification (:data:`_spec`) and
        * the given bound

        :param bound: Tuple containing the size for each template
        (number of states)
        '''

    def determine_guarantee_instances_dict(self, guarantee):
        '''
        Returns a dictionary that maps each template index to a range
        of instance indices of the particular template.

        :param guarantee:
        '''

    @property
    def is_initializable(self):
        '''
        Returns if the system is initializable (i.e., there exists
        an (unguarded) transition to the initial state)
        '''
        return False
