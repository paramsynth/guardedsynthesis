import math

from interfaces.parser_expr import Number, BinOp, UnaryOp, Bool, \
    Signal, ForallExpr, QuantifiedTemplateSignal
import helpers.visit as v


class ASTSignalCollectorVisitor:
    '''
    Visitor that collects all signals in a given specification formula and
    stores them in a signal list member
    '''
    # @DuplicatedSignature, pylint: disable=function-redefined
    def __init__(self):
        self.signals = []

    @v.on('node')
    def visit(self, node):
        pass

    @v.when(BinOp)
    def visit(self, node):  # @DuplicatedSignature
        self.visit(node.arg1)
        self.visit(node.arg2)

    @v.when(UnaryOp)
    def visit(self, node):  # @DuplicatedSignature
        self.visit(node.arg)

    @v.when(QuantifiedTemplateSignal)
    def visit(self, node):  # @DuplicatedSignature
        self.signals.append(node)

    @v.when(ForallExpr)
    def visit(self, node):  # @DuplicatedSignature
        self.visit(node.arg2)


class Visitor:
    def dispatch(self, node):  # TODO: clear: should accept Expr and return Expr
        if isinstance(node, BinOp):
            return self.visit_binary_op(node)

        if isinstance(node, UnaryOp):
            return self.visit_unary_op(node)

        if isinstance(node, Bool):
            return self.visit_bool(node)

        if isinstance(node, Signal):
            return self.visit_signal(node)

        if isinstance(node, Number):
            return self.visit_number(node)

        if isinstance(node, tuple):
            return self.visit_tuple(node)

        if isinstance(node, ForallExpr):
            return self.visit_forall(node)

        assert 0, 'unknown node type ' + str(node.__class__) + ': ' + str(node)

    def visit_binary_op(self, binary_op):
        return BinOp(binary_op.name,
                     self.dispatch(binary_op.arg1),
                     self.dispatch(binary_op.arg2))

    def visit_unary_op(self, unary_op):
        return UnaryOp(unary_op.name,
                       self.dispatch(unary_op.arg))

    def visit_bool(self,
                   bool_const):
        return bool_const

    def visit_signal(self, signal):
        return signal

    def visit_number(self, number):
        return number

    def visit_tuple(self, node):
        return node

    def visit_forall(self, node):
        # : :type: tuple
        binding_indices_visited = self.dispatch(node.arg1)
        # : :type: Expr
        quantified_expr_visited = self.dispatch(node.arg2)

        return ForallExpr(binding_indices_visited, quantified_expr_visited)


def get_log_bits(nof_processes):
    return int(max(1, math.ceil(math.log(nof_processes, 2))))
