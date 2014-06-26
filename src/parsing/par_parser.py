'''
Created on 20.02.2014

@author: Ayrat
'''

from logging import Logger



import parsing.par_parser_desc as par_parser
import thirdparty.ply as ply
import os



def parse_ltl(par_text:str, logger:Logger) -> dict:
    #TODO: current version of parser is very restrictive: it allows only the specs of the form:
    # Forall (i,j..) ass_i_j -> (Forall(k) gua_k * Forall(l,m) gua_l_m)
    # it is impossible to have:
    # (Forall(i) a_i  ->  Forall(k) g_k) * (Forall(i,j) a_i_j  ->  Forall(i) g_i)
    # what we can have is:
    # (Forall(i,j,k) ((a_i -> g_i)) * (Forall(i,j) a_i_j -> g_i)

    """ Return {section:data}, see sections in syntax_desc """

    if logger is not None:
        logger.info('parsing input spec..')
        
    
    section_name_to_data = dict(par_parser.parse(par_text))



    #TODO: check unknown signals
    return section_name_to_data