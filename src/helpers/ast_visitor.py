'''
Created on 21.02.2014

:author: simon
'''
import logging

from datastructures.specification import SpecFormula, Specification
from helpers import visit as v
from interfaces.parser_expr import *

# pylint: disable=function-redefined
LOG = logging.getLogger("ast_visitor")


class ASTInstantiateFormulaVisitor:
    '''
    Visitor which is used to instantiate a given
    :class:`datastructures.specification.SpecFormula`,
    i.e. replace all Forall expressions by conjunctions
    '''
    def __init__(self, spec):
        self._spec = spec
        self._schedule_values = dict(spec.get_schedule_values())
        self._schedule_variable_names = spec.get_scheduling_signals()

    @v.on('node')
    def visit(self, node, index_value_dict):
        return node

    @v.when(Number)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        return node

    @v.when(Bool)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        return node

    @v.when(SpecFormula)
    def visit(self, node, template_values_dict):  # @DuplicatedSignature
        # we assume that Forall expressions are the outmost expressions
        if not isinstance(node.formula, ForallExpr):
            return [node.formula]

        template_index_dict = node.template_instance_index_dict

        # list of ranges
        # reverse list
        multi_dict_list = [{x:k for x in v}
                           for k, v in template_index_dict.items()]

        index_template_dict = dict((k, v)
                                   for d in multi_dict_list
                                   for (k, v) in d.items())

        # get tuple of values for the template indices corresponding to
        # the templates the sorted index names belong to, e.g. (i,j,k),
        # where i -> template 1, j-> template 2, k-> template 3 results in
        # (template_values_dict[1],template_values_dict[2],
        #  template_values_dict[3])
        index_names = sorted(index_template_dict.keys())
        values_tuple = \
            tuple([template_values_dict[index_template_dict[template_index]]
                              for template_index in index_names])
        LOG.debug("Template index range: %s", str(values_tuple))

        # get instance for a certain index variable assignment
        def get_instance(values):
            assert(len(index_names) == len(values))

            # avoid double occurrences of single-template, multi-indexed
            # instantiations filter a) two-indexed i,j, where both i and j
            # have the same value or b) two-indexed i,j, where i>j
            # (e.g. (1,2) and (2,1) are redundant)
            if not node.is_multi_template_indexed \
                    and node.is_multi_indexed and \
                    not list(filter(lambda x: x != values[0], values)) or \
                    not all(values[i] <= values[i + 1]
                            for i in range(len(values) - 1)):
                return None

            value_dict = {index_names[i]: values[i]
                          for i in range(0, len(values))}

            inst = self.visit(node.formula, value_dict)
            LOG.debug("current value dictionary: %s "
                      " current instance: %s", value_dict, inst)
            return inst

        # get instances for all combination of variable assignments
        import itertools
        instances = [get_instance(values)
                     for values in itertools.product(*values_tuple)]

        # filter instances
        instances = [inst for inst in instances if inst is not None]
        LOG.debug("instances: %s", instances)
        return instances

    @v.when(ForallExpr)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        # dict values count must match quantified variables
        # assert(len(list(functools.reduce(lambda x,y: x + y,
        #        [f for f in template_index_dict.values()]))) >=
        #        len(node.binding_indices))
        return self.visit(node.arg2, index_value_dict)

    @v.when(BinOp)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        return BinOp(node.name,
                     self.visit(node.arg1, index_value_dict),
                     self.visit(node.arg2, index_value_dict))

    @v.when(UnaryOp)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        return UnaryOp(node.name, self.visit(node.arg, index_value_dict))

    @v.when(Signal)
    def visit(self, node, index_value_dict):  # @DuplicatedSignature
        if isinstance(node, QuantifiedTemplateSchedulerSignal):
            # replace is_scheduled_k_i by the conjunction that checks if the
            # Boolean scheduling variables are such that
            # is_scheduled_k_i is true

            # we currently only allow one index for template signals
            assert(len(node.binding_indices) == 1)

            schedule_var_assignments = \
                self._schedule_values[
                    (node.template_index,
                     index_value_dict[node.binding_indices[0]])]

            assert(len(schedule_var_assignments) ==
                   len(self._schedule_variable_names))
            sched_conjunctions = \
                [self._schedule_variable_names[i]
                 if schedule_var_assignments[i]
                 else UnaryOp('!', self._schedule_variable_names[i])
                 for i in range(0, len(schedule_var_assignments))]

            return and_expressions(sched_conjunctions)
        elif isinstance(node, QuantifiedTemplateSignal):
            # instantiate the quantified template signal

            # we currently only allow one index for
            # template signals (i.e. r_k_i_j is not possible)
            assert(len(node.binding_indices) == 1)
            signal = InstanceSignal(node.name,
                                    node.template_index,
                                    index_value_dict[node.binding_indices[0]])
        else:
            signal = Signal(node.name + '_' + str(node.template_index) + '_' +
                            '_'.join([str(index_value_dict[index_name])
                                      for index_name in node.binding_indices]))
        return signal
