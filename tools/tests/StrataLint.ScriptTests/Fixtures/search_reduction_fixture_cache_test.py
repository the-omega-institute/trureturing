"""Exact input and output invalidation of the test snapshot cache."""
import importlib.util
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location(
    "fixture_cache", ROOT / "scripts/search-reduction-fixtures.py")
cache = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cache)


class FixtureCacheTests(unittest.TestCase):
    def test_content_and_population_invalidation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            directory = root / "snapshot"
            source = root / "input.olean"
            source.write_bytes(b"compiled input")
            producer = root / "producer"
            producer.write_bytes(b"producer version")
            calls = []

            def produce():
                calls.append(True)
                directory.mkdir(exist_ok=True)
                for storage in ("tree", "members"):
                    (directory / storage).mkdir(exist_ok=True)
                    (directory / storage / "page.pickle").write_bytes(b"checked page")
                data = {
                    "header.json": {"scope": "test", "basis": "basis", "inputs": "1",
                                    "complete": True, "missing": [], "storage": "tree"},
                    "membership-header.json": {"inputs": "1", "complete": True,
                                               "missing": [], "storage": "members"},
                    "input-files.json": [str(source)],
                    "import-partitions.json": [["Fixture"]],
                }
                for name, value in data.items():
                    (directory / name).write_text(json.dumps(value))

            def ensure(roots=("Fixture",)):
                return cache.ensure_snapshot(
                    directory, "basis", list(roots), producer, produce, cache.ContentHashes())

            self.assertEqual(ensure(), "generated")
            self.assertEqual(ensure(), "reused")
            self.assertEqual(len(calls), 1)
            self.assertEqual(cache.ensure_snapshot(
                directory, "basis", ["Fixture"], root / "not-built",
                produce, cache.ContentHashes()), "reused")
            # Equal-size replacement still invalidates the content fingerprint.
            source.write_bytes(b"compiled other")
            self.assertEqual(ensure(), "generated")
            (directory / "members/page.pickle").write_bytes(b"corrupt page")
            self.assertEqual(ensure(), "generated")
            producer.write_bytes(b"changed producer")
            self.assertEqual(ensure(), "reused")
            with patch.object(cache, "VERSION", "different-explicit-format"):
                self.assertEqual(ensure(), "generated")
                self.assertEqual(ensure(), "reused")
            self.assertEqual(ensure(), "generated")
            self.assertEqual(ensure(("Fixture", "Another")), "generated")
            self.assertEqual(ensure(("Fixture", "Another")), "reused")
            self.assertEqual(len(calls), 6)

    def test_failed_or_incomplete_producer_cannot_publish_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            producer = root / "producer"
            producer.write_bytes(b"producer")
            directory = root / "snapshot"

            def fail():
                raise RuntimeError("producer failed")

            with self.assertRaisesRegex(RuntimeError, "producer failed"):
                cache.ensure_snapshot(directory, "basis", [], producer, fail, cache.ContentHashes())
            self.assertFalse((directory / "cache-sha256.json").exists())


if __name__ == "__main__":
    unittest.main()
