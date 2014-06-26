'''
Created on 07.03.2014

:author: simon
'''
from abc import ABCMeta, abstractmethod


class EncodingOptimization:
    '''
    Defines values that are used as encoding optimization switches
    '''
    NONE = 0
    LAMBDA_SCC = 1


class SMTEncoder(metaclass=ABCMeta):
    '''
    Base class for SMT encoders
    '''

    LABEL_GUARD_ENCODER = "label"
    STATE_GUARD_ENCODER = "state"

    def __init__(self, spec, architecture,
                 encoding_optimization=EncodingOptimization.NONE):
        '''
        Constructor
        '''
        self.spec = spec
        self.architecture = architecture
        self._encoding_optimization = encoding_optimization

    @abstractmethod
    def encode(self):
        '''
        Add formulae that describe the template skeletons and other
        helper functionality required by the UCT automata encoding
        method :meth:`encode_automata`
        '''
        pass

    @abstractmethod
    def encode_automata(self, automata_infos, global_cutoff):
        '''
        Encodes all automata in a given list

        Each automata_infos list item is a tuple containing

        * automaton index
        * automaton structure (nodes, transitions)
        * cut-off that is associated with the automaton (i.e., the underlying
          LTL formula)

        :param automata_infos: Automata infos list
        :param global_cutoff: Maximum cut-off used by the synthesis instance
        '''
        pass

    @abstractmethod
    def check(self):
        '''
        Checks if the encoding yields satisfiability

        In case of satisfiability a dictionary which maps template index to
        template model information is returned as part of a tuple.

        :return: (False, None) if the specification is not satisfiable
        for the given bound
        :return: (True, model) if the specification is satisfiable
        '''
        pass
