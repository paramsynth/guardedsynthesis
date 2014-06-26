'''
Created on 01.05.2014

@author: simon
'''

# pylint: disable=unused-import
from smt.api import encoder as api_encoder  # @UnusedImport
from smt.api.labelguarded import encoder as label_api_encoder  # @UnusedImport
from smt.api.stateguarded import encoder as state_api_encoder  # @UnusedImport
# pylint: enable=unused-import


class SMTEncoderFactory:
    def __init__(self):
        from smt.encoder_base import SMTEncoder

        base_classes = [SMTEncoder]
        self.encoders = {}
        while base_classes:
            # pylint: disable=no-member
            new_classes = {cls.get_encoder_type(): cls
                           for base_class in base_classes
                           for cls in base_class.__subclasses__()}
            base_classes = list(new_classes.values())

            if new_classes.__contains__(None):
                del new_classes[None]
            self.encoders.update(new_classes)

    def create(self, encoder_type):
        return self.encoders[encoder_type]
