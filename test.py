#!/usr/bin/env python

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
from __future__ import unicode_literals

import contextlib
import os
import subprocess
import time
import unittest


PEN_PATH = os.path.join(os.path.dirname(__file__), 'pen')


class Test(unittest.TestCase):

    def test_reverse_proxy(self):
        with pen(['-f', '-S', '1', '8888', 'savannah.nongnu.org:80']):
            curl = subprocess.Popen(['curl',
                                     '--silent',
                                     'http://127.0.0.1:8888'],
                                    stdout=subprocess.PIPE)
            self.assertIn('GNU', curl.communicate()[0].decode('utf-8'))
            self.assertEqual(0, curl.returncode)

    def test_handle_unwritable_file_gracefully(self):
        self.assertEqual(
            1,
            subprocess.call([PEN_PATH, '-f',
                             '-F', '/',
                             '-o', 'write', '/',
                             '8888', 'savannah.nongnu.org:80'],
                            stderr=subprocess.PIPE))


@contextlib.contextmanager
def pen(arguments):
    process = subprocess.Popen([PEN_PATH] + arguments)

    time.sleep(2)

    try:
        yield process
    finally:
        process.kill()


if __name__ == '__main__':
    unittest.main()
