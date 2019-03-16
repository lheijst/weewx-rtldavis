# installer for the weewx-rtldavis driver
# Copyright 2019 Matthew Wall and Luc Heijst
# Distributed under the terms of the GNU Public License (GPLv3)

from setup import ExtensionInstaller

def loader():
    return RtldavisInstaller()

class RtldavisInstaller(ExtensionInstaller):
    def __init__(self):
        super(RtldavisInstaller, self).__init__(
            version="0.8",
            name='rtldavis',
            description='Capture data from rtldavis',
            author="Matthew Wall",
            author_email="mwall@users.sourceforge.net",
            files=[('bin/user', 
                   ['bin/user/rtldavis.py'])
			]
        )
