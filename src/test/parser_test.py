'''
Created on 20.02.2014

@author: simon
'''
import unittest
import logging

import parsing.par_parser as parser

SIMPLE_SPEC = """
[GENERAL]
templates: 2

[INPUT_VARIABLES] #no support of global variables => all the variables are assumed to be indexed!
r_0;r_1;

[OUTPUT_VARIABLES]
g_0;g_1;

[ASSUMPTIONS]
Forall (i) r_0_i=0;
Forall (i) G(F((r_0_i=0)+(g_0_i=0)));
Forall (i) r_1_i=0;
Forall (i) G(F((r_1_i=0)+(g_1_i=0)));

[GUARANTEES]
Forall (i) g_0_i=0;
Forall (i) g_1_i=0;
Forall (i,j) G(!((g_0_i=1) * (g_0_j=1)));
Forall (i,j) G(!((g_0_i=1) * (g_1_j=1)));
Forall (i,j) G(!((g_1_i=1) * (g_1_j=1)));
"""


# par_parser.bparser.parse(input=SIMPLE_SPEC)
parser.parse_ltl(SIMPLE_SPEC, logging.getLogger())
