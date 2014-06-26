'''
Created on 20.02.2014

@author: simon
'''
import logging

from datastructures.specification import ArchitectureAssumption, \
    ArchitectureGuarantee
from interfaces.parser_expr import ForallExpr, QuantifiedTemplateSignal, \
    BinOp, UnaryOp, QuantifiedTemplateSchedulerSignal
from datastructures.exceptions import ArchitectureException
from architecture.architecture_base import Architecture
from enum import Enum

LOG = logging.getLogger("arch")


class GuardedArchitectureType(Enum):  # pylint: disable=too-few-public-methods
    '''
    Enum for type of guard architectures
    '''
    conjunctive_guards = 1
    disjunctive_guards = 2


class GuardedArchitecture(Architecture):
    '''
    Base class for guarded architectures
    '''
    def __init__(self, spec):
        Architecture.__init__(self, spec)

    def get_architecture_assumptions(self, template_indices):
        arch_assumptions = [self._get_architecture_assumptions(template_index)
                            for template_index in template_indices]
        return arch_assumptions

    def get_architecture_guarantees(self, template_indices):
        guarantees = \
            [ArchitectureGuarantee(
                ForallExpr(
                    ('j'),
                    UnaryOp(
                        'G',
                        UnaryOp(
                            'F',
                            QuantifiedTemplateSignal(
                                'init',
                                template_index,
                                ('j'))))))
             for template_index in template_indices]
        return guarantees

    def get_architecture_properties(self, template_indices):
        assumptions = \
            [ArchitectureAssumption(
                ForallExpr(
                    ('j'),
                    UnaryOp(
                        'G',
                        UnaryOp(
                            'F',
                            QuantifiedTemplateSchedulerSignal(
                                template_index,
                                ('j'))))))
             for template_index in template_indices]

        guarantees = \
            [ArchitectureGuarantee(
                ForallExpr(
                    ('j'),
                    UnaryOp(
                        'G',
                        UnaryOp(
                            'F',
                            QuantifiedTemplateSignal(
                                'enabled',
                                template_index,
                                ('j'))))))
             for template_index in template_indices]

        return [(assumptions, guarantee) for guarantee in guarantees]

    def _get_architecture_assumptions(self, template_index):
        '''
        Returns fair scheduling assumption GF moves_k^i for particular template
        '''
        assumption = \
            ArchitectureAssumption(
                ForallExpr(
                    ('j'),
                    UnaryOp(
                        'G',
                        UnaryOp(
                            'F',
                            BinOp(
                                '*',
                                QuantifiedTemplateSignal(
                                    'enabled', template_index, ('j')),
                                QuantifiedTemplateSchedulerSignal(
                                    template_index, ('j')))))))
        return assumption

    def determine_cutoffs(self, bound):
        # determine how many instances we need for each template
        cutoff = list(self._get_architecture_cutoff(bound))
        LOG.debug("Architecture specific cut-off: %s", str(cutoff))

        guarantee_cutoffs_tuples = \
            [(guarantee,
              self._get_guarantee_cutoff_and_update_global_cutoff(
                  guarantee, cutoff, bound))
             for guarantee in self._spec.guarantees]

        LOG.info("Bound: %s => cutoff: %s", bound, cutoff)
        LOG.info(guarantee_cutoffs_tuples)
        return tuple(cutoff), guarantee_cutoffs_tuples

    def determine_guarantee_instances_dict(self, guarantee):
        if guarantee.is_multi_template_indexed:
            if len(guarantee.template_indices) != 2 or \
                    len(guarantee.indices) != 2:
                raise ArchitectureException("Unsupported multi-template "
                                            "guarantee")
            return {i: range(1) for i in guarantee.template_indices}

        assert len(guarantee.template_indices) == 1

        if not 1 <= len(guarantee.indices) <= 2:
            raise ArchitectureException("Unsupported single-template "
                                        "guarantee")
        return {i: range(len(guarantee.indices))
                for i in guarantee.template_indices}

    def _get_guarantee_cutoff_and_update_global_cutoff(self, guarantee,
                                                       global_cutoff, bound):
        '''
        Returns the cut-off for a specific guarantee and checks if it exceeds
        the current global cut-off. In this case the global cut-off is updated
        s.t. each element of the guarantee-cutoff is less or equal than the
        particular global cut-off element

        :param guarantee: Guarantee whose cut-off should be determined
        :param global_cutoff: Current global cut-off as list
        :param bound: Tuple of template bounds used to calculate the cut-off
        :return Guarantee cut-off
        '''
        guarantee_cutoff = self._get_guarantee_cutoff(guarantee, bound)

        # update global cutoff
        for i in range(len(global_cutoff)):
            global_cutoff[i] = max(global_cutoff[i], guarantee_cutoff[i])
        return guarantee_cutoff

    def _get_guarantee_cutoff(self, guarantee, bound):
        '''
        Determines the cut-off for a given guarantee
        (implemented in subclasses)

        :param guarantee:
        :param bound:
        '''
        # implemented by subclasses
        raise NotImplementedError()

    def _get_architecture_cutoff(self, bound):
        '''
        Returns the architecture specific cut-off that is necessary in
        order to avoid deadlocks

        :param bound: current template bound
        '''
        raise NotImplementedError()

    @classmethod
    def get_type_by_id(cls, name):
        '''
        Returns the class which corresponds to a name

        :param cls:
        :param name: :class:`GuardedArchitectureType` value that
                     uniquely identifies the architecture type
        '''
        for cls in cls.__subclasses__():  # pylint: disable=no-member
            if cls.get_type_name() == name:
                return cls
        return None


class DisjunctiveGuardedArchitecture(GuardedArchitecture):
    '''
    Disjunctive Guarded Architecture

    A disjunctive guarded architecture A consists of templates that are based
    on guarded LTSs. Here, all guards are disjunctive.

    For the given fairness constraints, there are no deadlocks in disjunctive
    guarded systems. Thus, there is no deadlock cut-off. The property
    cut-offs are

    * :math:`(2|T_1|, ..., 2*|T_l|+1, ..., 2|T_k|)` for single-indexed
      properties that include instances of template l
    * :math:`(2|T_1|, ..., 2*|T_l|+2, ..., 2|T_k|)` for double-indexed
      properties that include instances of template l
    * :math:`(2|T_1|, ..., 2*|T_l|+1, ..., 2*|T_m|+1, ... , 2|T_k|)` for
      double-indexed properties that include instances of template l and m
    '''

    def __init__(self, spec):
        GuardedArchitecture.__init__(self, spec)

    def _get_guarantee_cutoff(self, guarantee, bound):
        guarantee_cutoff = None
        if guarantee.is_multi_template_indexed:
            if len(guarantee.template_indices) != 2 or \
                    len(guarantee.indices) != 2:
                raise ArchitectureException("Unsupported multi-template "
                                            "guarantee")
            guarantee_cutoff = tuple(
                [2 * bound[i] +
                 (1 if guarantee.template_indices.__contains__(i)
                  else 0) for i in range(len(bound))])
        else:
            if len(guarantee.template_indices) != 1 or \
                    not 1 <= len(guarantee.indices) <= 2:
                raise ArchitectureException("Unsupported single-template "
                                            "guarantee")
            guarantee_cutoff = tuple(
                [2 * bound[i] + (len(guarantee.indices)
                                 if guarantee.template_indices.__contains__(i)
                                 else 0) for i in range(len(bound))])
        return guarantee_cutoff

    def _get_architecture_cutoff(self, bound):
        return tuple([max(2 * b + 1, 1) for b in bound])

    @classmethod
    def get_type_name(cls):
        return GuardedArchitectureType.disjunctive_guards


class ConjunctiveGuardedArchitecture(GuardedArchitecture):
    '''
    Conjunctive Guarded Architecture

    A conjunctive guarded architecture A consists of templates that are based
    on guarded LTSs. Here, guards are conjunctive and contain all templates'
    initial states.

    For the given fairness constraints, we need at most 2|T_l|-1 processes
    in order to detect deadlocks. Thus, the deadlock cut-off is
    (2|T_1|-1, ..., 2|T_k|-1). For deadlock-free systems, the property
    cut-offs are

    * (1, ..., 1, ..., 1) for single-indexed properties that include
    instances of template \mathcal{T}_l
    * (1, ..., 2, ..., 1) for double-indexed properties that include
    instances of template \mathcal{T}_l
    * (1, ..., 1, ..., 1, ... 1) for double-indexed properties that
    include instances of template \mathcal{T}_l and \mathcal{T}_m
    '''
    def __init__(self, spec):
        GuardedArchitecture.__init__(self, spec)

    def _get_guarantee_cutoff(self, guarantee, bound):
        guarantee_cutoff = None
        if guarantee.is_multi_template_indexed:
            if len(guarantee.template_indices) != 2 or \
                    len(guarantee.indices) != 2:
                raise ArchitectureException("Unsupported multi-template "
                                            "guarantee")
            guarantee_cutoff = \
                tuple([1 + (1 if guarantee.template_indices.__contains__(i)
                            else 0) for i in range(len(bound))])
        else:
            if len(guarantee.template_indices) != 1 or \
                    not 1 <= len(guarantee.indices) <= 2:
                raise ArchitectureException("Unsupported single-template "
                                            "guarantee")
            guarantee_cutoff = \
                tuple([1 + (len(guarantee.indices)
                            if guarantee.template_indices.__contains__(i)
                            else 0) for i in range(len(bound))])
        return guarantee_cutoff

    def _get_architecture_cutoff(self, bound):
        return tuple([max(2 * b - 1, 1) for b in bound])

    @classmethod
    def get_type_name(cls):
        return GuardedArchitectureType.conjunctive_guards
