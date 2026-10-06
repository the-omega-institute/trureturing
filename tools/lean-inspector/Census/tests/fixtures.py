"""Run the independent census data and certificate contract tests."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
if __name__ == "__main__":
    suite = unittest.defaultTestLoader.discover(str(pathlib.Path(__file__).parent), pattern="test_*.py")
    raise SystemExit(not unittest.TextTestRunner().run(suite).wasSuccessful())
