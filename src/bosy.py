'''
Main program logic of parameterized bounded synthesis for guarded systems
'''
import logging

from datastructures import specification
from datastructures.specification import ArchitectureGuarantee
from helpers import automata_helper
from helpers.ast_visitor import ASTInstantiateFormulaVisitor
from interfaces.parser_expr import and_expressions, BinOp
from translation2uct.ltl2automaton import Ltl2UCW
from smt.encoder import SMTEncoderFactory
import config

LOG = logging.getLogger("bosy")


class BoundedSynthesis:

    def __init__(self, spec_filename, architecture):
        """
        :param spec_filename: path of LTL specification
        :param architecture: class which represents the desired
                             system architecture
        """
        self.min_bound = None
        self.max_increments = None
        self.encoder_type = None
        self.instance_count = None
        self.encoder_optimization = None
        self.test_mode = False

        self.spec_filename = spec_filename

        # load specification
        self.spec = specification.Specification(filename=spec_filename)
        # initialize architecture
        self.arch = architecture(self.spec)

        self.ltl2ucw = Ltl2UCW(config.LTL3BA_PATH)

    def solve(self):
        '''
        Bounded synthesis

        Passes the following steps iteratively until the solver returns
        SAT in the solving step.

        * Set bound
        * Determine cut-off
        * Instantiate properties and create UCT automata
        * Encode formula in SMT
        * Solve

        :return: model or None if no model was found
        '''
        self.spec.bound = self.min_bound

        status = None
        model = None

        for round_index in range(self.max_increments + 1):
            # increase bound for all templates
            self.spec.bound = tuple([b + round_index for b in self.min_bound])
            LOG.info("Set bound to %s", str(self.spec.bound))

            # recalculate cut-off
            self.spec.cutoff, guarantee_cutoffs_list = \
                self.arch.determine_cutoffs(self.spec.bound)

            # avoid that cut-off becomes larger than instance count
            if any([self.spec.cutoff[i] > self.instance_count[i] for i in
                    range(len(self.spec.cutoff))]):
                orig_spec_cutoff = self.spec.cutoff
                self.spec.cutoff = self._truncate_cutoff(self.spec.cutoff)
                LOG.info("Truncate maximum cut-off from %s to %s",
                             orig_spec_cutoff, self.spec.cutoff)
                guarantee_cutoffs_list = \
                    [(guarantee, self._truncate_cutoff(cutoff))
                     for guarantee, cutoff in guarantee_cutoffs_list]

            if self.test_mode:
                # in test mode, we set the cut-off to the instance count
                self.spec.cutoff = self.instance_count
                guarantee_cutoffs_list = [(guarantee, self.spec.cutoff)
                                          for guarantee, _ in
                                          guarantee_cutoffs_list]

            LOG.info("Cut-Off: %s", str(self.spec.cutoff))

            # add architecture guarantees with max. cut-off
            # (architecture guarantees must hold for all
            # instances in the system)
            arch_guarantees = self.arch.get_architecture_guarantees(
                range(0, self.spec.templates_count))
            arch_guarantee_cutoffs_list = [(guarantee, self.spec.cutoff)
                                           for guarantee in arch_guarantees]
            guarantee_cutoffs_list = (arch_guarantee_cutoffs_list +
                                      guarantee_cutoffs_list)

            LOG.debug("-------------------------------------------")
            LOG.debug("Guarantees")
            for guarantee, guarantee_cutoff in guarantee_cutoffs_list:
                LOG.debug("%s --> cut-off: %s)",
                          guarantee, guarantee_cutoff)
            LOG.debug("-------------------------------------------")

            # build assumptions set
            if len(self.spec.assumptions) > 0:
                raise Exception("Specification assumptions are "
                                "currently not supported!")

            arch_assumptions = self.arch.get_architecture_assumptions(
                range(0, self.spec.templates_count))
            assumptions = self.spec.assumptions + arch_assumptions

            # create properties
            # properties are either tuples (assumption, guarantee) of
            # quadruples (assumption, guarantee, cutoff, ignore_cutoff)
            # ignore_cutoff is set if the guarantee-specific cut-off is
            # larger than the number of specified instances
            properties = [(assumptions,
                           guarantee,
                           guarantee_cutoff,
                           any([guarantee_cutoff[i] > self.spec.cutoff[i]
                                for i in range(len(self.spec.cutoff))]))
                          for (guarantee, guarantee_cutoff)
                          in guarantee_cutoffs_list]

            # add architecture properties
            arch_properties = [tuple(list(p) + [self.spec.cutoff, False])
                               for p in self.arch.get_architecture_properties(
                                   range(0, self.spec.templates_count))]
            properties = arch_properties + properties

            LOG.info("-------------------------------------------")
            LOG.info("Properties")
            for assumptions, guarantee, \
                    guarantee_cutoff, ignore_cutoff in properties:
                LOG.info("(%s, %s) --> cut-off: %s, ignore: %s)",
                         assumptions, guarantee,
                         guarantee_cutoff, ignore_cutoff)
            LOG.info("-------------------------------------------")

            # instantiate properties
            instantiated_properties = \
                self.instantiate_properties(properties,
                                            self.spec.cutoff)

            # get automaton for each property
            property_automata = [self.ltl2ucw.convert(prop)
                                 for prop in instantiated_properties]

            for i, prop in enumerate(instantiated_properties):
                LOG.info(prop)
                LOG.info("\t states: %s", len(property_automata[i].nodes))

            # encode automata
            encoder = SMTEncoderFactory().create(self.encoder_type)(
                self.spec, self.arch, self.encoder_optimization)
            encoder.encode()

            LOG.debug(encoder.encoder_info.solver.check())

            encoder.encode_automata([(property_automata[i],
                                      i,
                                      i < len(arch_properties),
                                      properties[i][2] if not properties[i][3]
                                      else self.spec.cutoff)
                                     for i in range(len(property_automata))],
                                    self.spec.cutoff)
            status, model = encoder.check()

            for a in encoder.encoder_info.solver.assertions():
                LOG.debug(a)

#             m = encoder.encoder_info.solver.model()
#             for m in model:
#                 print(m)

            LOG.info("Status: %s", status)
            LOG.info("Model: %s", model)

            # extract solution
            if status:
                return model

    def _truncate_cutoff(self, cutoff):
        return tuple([min(self.instance_count[i], cutoff[i])
                      for i in range(len(self.instance_count))])

    def instantiate_properties(self, properties, cutoff):
        '''
        Instantiates the quantified property formulas

        :param properties: list of tuples (assumption, guarantee) or
               (assumption, guarantee, guarantee_cutoff,
                ignore_guarantee_cutoff)
        :param cutoff: global cut-off
        '''
        return [self.instantiate_property(prop, cutoff) for prop in properties]

    def instantiate_property(self, prop, cutoff):
        '''
        Instantiates the given property

        :param prop: See ``properties`` in :func:`instantiate_properties`
        :param cutoff:
        '''
        # extract assumptions and guarantees
        assumptions, guarantee = prop[:2]

        LOG.debug(prop)
        # there is no special cut-off for architecture guarantees
        # and architecture properties
        use_default_cutoff = len(prop) <= 2 or prop[3]
        guarantee_cutoff = cutoff if use_default_cutoff else prop[2]

        # avoid using a cut-off that requires more instances than we want
        if use_default_cutoff:
            LOG.info("Ignore cut-off for property %s because %s > %s",
                     str(prop[0]) + " -> " + str(prop[1]), prop[2], cutoff)

        ast_visitor = ASTInstantiateFormulaVisitor(self.spec)

        assumption_guarantee_instances_dict = \
            {i: range(guarantee_cutoff[i])
             for i in range(len(guarantee_cutoff))}
        assumption_instances_dict = assumption_guarantee_instances_dict

        # instantiate guarantees
        guarantee_instances_dict = assumption_guarantee_instances_dict
        if not isinstance(guarantee, ArchitectureGuarantee) \
                and not use_default_cutoff:
            # get instance dict for guarantee according to cut-off
            guarantee_instances_dict = \
                self.arch.determine_guarantee_instances_dict(guarantee)

        instantiated_guarantees = and_expressions(
            [conjunct for conjunct in
             ast_visitor.visit(guarantee, guarantee_instances_dict)])
        LOG.debug("Guarantees instantiated: %s", instantiated_guarantees)

        instantiated_assumptions = None
        if len(assumptions) and \
                self.is_liveness_property(instantiated_guarantees):
            # instantiate assumptions
            instantiated_assumptions = \
                and_expressions([conjunct for formula in assumptions
                                 for conjunct in
                                 ast_visitor.visit(formula,
                                                   assumption_instances_dict)])

        LOG.debug("Assumptions instantiated: %s", instantiated_assumptions)

        # return implication or just guarantees
        if instantiated_assumptions is not None:
            return BinOp('->', instantiated_assumptions,
                         instantiated_guarantees)
        else:
            return instantiated_guarantees

    def is_liveness_property(self, guarantee):
        '''
        Checks whether the given guarantee is a liveness guarantee
        :param guarantee:
        '''
        automaton = self.ltl2ucw.convert(guarantee)
        return not automata_helper.is_safety_automaton(automaton)


def print_spec_formulas(*spec_formulas):
    '''
    Prints some information for the given specification formulas
    '''
    for spec_formula in spec_formulas:
        print("Formula:", spec_formula.formula)
        print("  Indices:   ", str(spec_formula.indices)[1:-2])
        print("  Templates: ", str(spec_formula.template_indices)[1:-1])
        print("  Template-I:",
              list(spec_formula.template_instance_index_dict.items())[1:-1])
        print("")
