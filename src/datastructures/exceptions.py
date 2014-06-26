'''
Created on 13.03.2014

@author: simon
'''


class ArchitectureException(Exception):
    def __init__(self, message):
        Exception.__init__(self, message)


class SpecificationException(Exception):
    def __init__(self, message):
        Exception.__init__(self, message)
