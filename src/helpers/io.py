'''
Created on 13.03.2014

@author: simon
'''

import os
import errno


def mkdir_p(path):
    '''
    Equivalent to mkdir -p

    source: http://stackoverflow.com/questions/600268/
    :param path:
    '''
    try:
        os.makedirs(path)
    except OSError as exc:  # Python >2.5
        if exc.errno == errno.EEXIST and os.path.isdir(path):
            pass
        else:
            raise exc
