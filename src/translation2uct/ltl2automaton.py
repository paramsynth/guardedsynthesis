from functools import lru_cache
from itertools import chain
import logging
from helpers.shell import execute_shell
from interfaces.automata import Automaton
from interfaces.parser_expr import UnaryOp, Expr, Signal
from translation2uct.ast_to_ltl3ba import ConverterToLtl2BaFormatVisitor
from translation2uct.ltl2ba import parse_ltl2ba_ba


def _negate(expr:Expr) -> Expr:
    return UnaryOp('!', expr)


def _assert_are_signals_in_labels(nodes):  # TODO: remove me after debugging phase finished
    for n in nodes:
        for label in n.transitions:
            for s in label.keys():
                assert isinstance(s, Signal)


class Ltl2UCW:
    def __init__(self, ltl2ba_path):
        self._execute_cmd = ltl2ba_path + ' -M -f'
        self._logger = logging.getLogger(__name__)

    @lru_cache()
    def convert(self, expr:Expr) -> Automaton:
        self._logger.debug('Ltl2UCW: converting..')

        format_converter = ConverterToLtl2BaFormatVisitor()
        property_in_ltl2ba_format = format_converter.dispatch(_negate(expr))
	
        self._logger.debug("------------------------------------------")
        self._logger.debug(property_in_ltl2ba_format)
        self._logger.debug("------------------------------------------")


        rc, ba, err = execute_shell('{0} "{1}"'.format(self._execute_cmd, property_in_ltl2ba_format))
        assert rc == 0, str(rc) + ', err: ' + str(err) + ', out: ' + str(ba)
        assert (err == '') or err is None, err
        self._logger.debug(ba)

        initial_nodes, rejecting_nodes, nodes = parse_ltl2ba_ba(ba, format_converter.signal_by_name)

        _assert_are_signals_in_labels(list(chain(*initial_nodes)) + rejecting_nodes + nodes)

        automaton = Automaton(initial_nodes, rejecting_nodes, nodes, name=str(property_in_ltl2ba_format))
        return automaton
