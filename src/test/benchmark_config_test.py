'''
Created on 15.06.2014

@author: simon
'''
import unittest
from helpers import benchmark_config


class BenchmarkConfigTest(unittest.TestCase):

    def testSimpleBenchmark(self):
        content = """
# filename                          type              instances    bounds    max_increment  optimize runs
conj_mutual_exclusion_in_2.ltl      conjunctive_guards       5:10         2        2               scc,labels,no-test     5
#conj_mutual_exclusion_in_2.ltl      conjunctive_guards       2:10         3        2               scc     5
"""
        benchmark_config.parse_config(content)


if __name__ == "__main__":
    # import sys;sys.argv = ['', 'Test.testName']
    unittest.main()
