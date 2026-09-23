"""Native inspector regression owner assembled from bounded test groups."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_native_support import NativeTestSupport
from test_native_invalidation import *
from test_native_publication import *
from test_native_recovery import *
from test_native_packaging import *
from test_native_reuse import *

class NativeTests(NativeTestSupport, NativeInvalidationTests, NativePublicationTests,
                  NativeRecoveryTests, NativePackagingTests, NativeReuseTests, unittest.TestCase):
    pass

if __name__ == '__main__':
    unittest.main()
