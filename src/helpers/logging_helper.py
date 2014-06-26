import logging


def log_entrance(logger=logging.getLogger(), log_level=logging.INFO):
    def wrap(func):
        def wrapped_func(*args):
            logger.log(log_level, func.__name__)
            return func(*args)

        return wrapped_func
    return wrap


def verbosity_to_log_level(verbose):
    # setup logger
    log_levels = [logging.NOTSET, logging.CRITICAL, logging.ERROR,
                  logging.WARNING, logging.INFO, logging.DEBUG]
    log_level = log_levels[-1]
    if verbose is not None and 0 <= verbose < len(log_levels):
        log_level = log_levels[verbose]
    return log_level
