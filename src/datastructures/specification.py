

from math import ceil, log
from collections import defaultdict

import interfaces.parser_expr as parser_expr
import parsing.par_parser as par_parser
import parsing.par_lexer_desc as par_lexer_desc
from interfaces.parser_expr import Signal
from datastructures.exceptions import SpecificationException
from parsing.helpers import ASTSignalCollectorVisitor


class Specification(object):
    '''
    Encapsulates an LTL specification and provides functionality to read a
    given LTL specification file
    '''

    def __init__(self, filename=None, content=None):
        '''
        Constructor
        '''
        try:

            # read content
            if filename is not None:
                with open(filename, 'r') as fh:
                    content = fh.read()
            assert(content is not None)
            spec_dict = par_parser.parse_ltl(content, None)

            # global system parameters
            system_parameters = {t[0]: t[1] for t
                                 in spec_dict[par_lexer_desc.PAR_GENERAL]}
            self.__system_parameters = system_parameters

            self.templates_count = int(
                system_parameters[par_lexer_desc.PAR_GENERAL_TEMPLATE_COUNT])
            self.templates = [Template(i)
                              for i in range(0, self.templates_count)]

            # signals
            for sig in spec_dict[par_lexer_desc.PAR_INPUT_VARIABLES]:
                assert(type(sig.template_index) is int)
                self.templates[sig.template_index].inputs.append(sig)
            for sig in spec_dict[par_lexer_desc.PAR_OUTPUT_VARIABLES]:
                self.templates[sig.template_index].outputs.append(sig)

            # assumptions
            self.assumptions = [Assumption(formula) for formula
                                in spec_dict[par_lexer_desc.PAR_ASSUMPTIONS]]
            self.guarantees = [Guarantee(formula) for formula
                               in spec_dict[par_lexer_desc.PAR_GUARANTEES]]

            # bound
            self.bound = (0,) * self.templates_count

            # cut-off
            self.cutoff = (0,) * self.templates_count
        except Exception as e:
            raise SpecificationException("Error while reading "
                                         "specification: %s" % e)

    @property
    def bound(self):
        '''
        Bound for the current template sizes (number of LTS states)

        This variable is used by the solving units.
        '''
        return self._bound

    @bound.setter
    def bound(self, value):
        assert(len(value) == self.templates_count)
        assert(len(self.templates) == self.templates_count)

        self._bound = value
        for template_index in range(0, self.templates_count):
            self.templates[template_index].bound = value[template_index]

    @property
    def bound_sum(self):
        '''
        Sum of maximal number of LTS states (i.e., sum over all template sizes)
        '''
        return sum(self._bound)

    @property
    def cutoff(self):
        '''
        Global cut-off

        This variable is used by the solving units.
        '''
        return self._cutoff

    @cutoff.setter
    def cutoff(self, value):
        assert(len(value) == self.templates_count)
        assert(len(self.templates) == self.templates_count)

        self._cutoff = value
        for template_index in range(0, self.templates_count):
            self.templates[template_index].cutoff = value[template_index]

    @property
    def cutoff_sum(self):
        '''
        Sum over cut-offs (i.e., overall number of instances in the
        distributed system)
        '''
        return sum(self._cutoff)

    def get_schedule_values(self):
        """
        Returns tuple ((k,i), sched_value), where sched_value is
        the boolean assignment (low endian)
        """

        # list of (template_index, instance_index) tuples based on the currently stored cut-off
        template_instance_tuple_list = \
            [(template_index, inst_index)
             for template_index in range(0, len(self.cutoff))
             for inst_index in range(0, self.cutoff[template_index])]

        def _get_bool_assignment(index_tuple, index_tuple_position):
            '''
            Calculates the assignment of the boolean scheduling variables s.t.
            the particular process identified by (template_index, instance_index)
            is scheduled.

            :param index_tuple: Process identifying tuple (k,i)
            :param index_tuple_position: Index of the tuple in the (k,i) tuple list
            '''
            # binary representation of the tuple index
            binval = bin(index_tuple_position)[2:]
            bool_assignment = list(map(lambda i: binval[i] == '1',
                                       range(0, len(binval))))
            # prepend False
            bool_assignment = [False] * (self.get_scheduling_size() -
                                         len(bool_assignment)) + bool_assignment
            assert(len(bool_assignment) == self.get_scheduling_size())
            return bool_assignment

        return [(template_instance_tuple_list[i],
                 _get_bool_assignment(template_instance_tuple_list[i], i))
                for i in range(0, len(template_instance_tuple_list))]

    def get_scheduling_size(self):
        '''
        Returns the number of required Boolean scheduling variables for
        the given cut-off stored in :data:`cutoff`
        '''
        return max(ceil(log(self.cutoff_sum, 2)), 1)

    def get_scheduling_signals(self):
        '''
        Returns a list of signals that represent the Boolean scheduling
        variables

        The number of scheduling signals is determined by
        :meth:`get_scheduling_size`
        '''
        return [Signal('sched_%d' % i)
                for i in reversed(range(0, self.get_scheduling_size()))]


class Template:
    '''
    Encapsulates the specification-side information about a template
    '''
    def __init__(self, template_index):
        self.template_index = template_index
        self.inputs = []
        self.outputs = []
        self.bound = 0
        self.cutoff = 0

    @property
    def initial_states(self):
        '''
        Returns a set of integers that represent the initial states

        Currently, we support a single initial state, which is assumed to be
        state 0.
        '''
        assert(self.bound > 0)
        return {0}


class SpecFormula:
    '''
    Represents a formula defined in the LTL specification
    '''
    def __init__(self, formula):
        assert(isinstance(formula, parser_expr.ForallExpr))
        self._formula = formula

        # get signals
        signal_collector = ASTSignalCollectorVisitor()
        signal_collector.visit(formula)

        # tuples of template index and corresponding indices
        template_instance_index_tuples = [(s.template_index, s.binding_indices)
                                          for s in signal_collector.signals]
        self._template_indices = set([index for index, _
                                      in template_instance_index_tuples])

        # dictionary mapping template index to index variables
        self._template_instance_index_dict = defaultdict(set)
        for sig_info in template_instance_index_tuples:
            self._template_instance_index_dict[sig_info[0]] = \
            self._template_instance_index_dict[sig_info[0]].union(set(sig_info[1]))

        assert(
            len(self._template_instance_index_dict.keys()) == 1 or
            len(set.intersection(*[set(index_list) for index_list in
                                   self._template_instance_index_dict.values()])) == 0)

        # we only allow a maximum of two process templates
        assert(len(self._template_instance_index_dict.keys()) > 0)
        assert(len(self._template_instance_index_dict.keys()) <= 2)
        assert(len(self.indices) > 0)

        # if we have two templates indices, we allow at most two indices
        assert(len(self._template_indices) == 1 or len(self.indices) == 2)

    @property
    def formula(self):
        '''
        Returns LTL formula
        '''
        return self._formula

    @property
    def indices(self) -> tuple:
        '''
        Returns letters that are used as quantified index variables
        '''
        return self._formula.binding_indices

    @property
    def template_indices(self) -> set:
        '''
        Returns the indices of templates which are contained in the formula
        '''
        return self._template_indices

    @property
    def template_instance_index_dict(self) -> defaultdict:
        '''
        Returns a dict that maps template indices to the letters
        that represent quantified indices of the particular template
        in the formula
        '''
        return self._template_instance_index_dict

    @property
    def templates_count(self):
        '''
        Number of templates that the formula uses
        '''
        return len(self._template_instance_index_dict.keys())

    @property
    def is_multi_template_indexed(self):
        '''
        Returns whether the formula specifies at least two different
        templates
        '''
        return len(self._template_instance_index_dict.keys()) > 1

    @property
    def is_multi_indexed(self):
        '''
        Returns whether there are at least two index variables
        '''
        return len(self.indices) > 1

    @property
    def is_full_sized(self):
        '''
        Returns whether the  quantified indices need to be instantiated for
        all possible process indices (their combinations, respectively), i.e.,
        there is no cut-off.
        '''
        return False

    def __repr__(self):
        return str(self._formula)
    __str__ = __repr__


class Assumption(SpecFormula):
    '''
    Represents an assumption
    '''
    @property
    def is_full_sized(self):
        return True


class ArchitectureAssumption(Assumption):
    '''
    Represents an architecture specific assumption
    '''
    pass


class Guarantee(SpecFormula):
    '''
    Represents a guarantee formula
    '''
    pass


class ArchitectureGuarantee(Guarantee):
    '''
    Represents an architecture specific guarantee
    '''
    @property
    def is_full_sized(self):
        return True


