#!/usr/bin/env python

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
from __future__ import unicode_literals

import contextlib
import subprocess
import time
import unittest


class Test(unittest.TestCase):

    def test_reverse_proxy(self):
        with pen(['-f', '-S', '1', '8888', 'savannah.nongnu.org:80']):
            curl = subprocess.Popen(['curl',
                                     '--silent',
                                     'http://127.0.0.1:8888'],
                                    stdout=subprocess.PIPE)
            self.assertIn('GNU', curl.communicate()[0].decode('utf-8'))


@contextlib.contextmanager
def pen(arguments):
    process = subprocess.Popen(['./pen'] + arguments)

    time.sleep(2)
    yield process

    process.kill()


if __name__ == '__main__':
    unittest.main()
