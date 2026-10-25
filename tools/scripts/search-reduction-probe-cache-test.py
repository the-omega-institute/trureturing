#!/usr/bin/env python3
"""Regression checks for input binding and authenticated cache corruption."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "probe_cache", Path(__file__).with_name("search-reduction-probe-cache.py"))
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class ProbeCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix="probe-cache-test-",
                                             dir="build/lean-inspector")).absolute()
        self.key = bytes(range(32))

    def test_each_semantic_input_invalidates_old_result(self):
        files = ["request.lean", "tools/lean-inspector/Judge.lean",
                 "index/page.json", "library/Source.olean", "lake-manifest.json"]
        for name in files + ["tools/scripts/search-reduction-probe-cache.py"]:
            path = self.directory / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"first")
        root = self.directory / "cache"
        root.mkdir()
        before_cwd = Path.cwd()
        try:
            os.chdir(self.directory)
            with patch.dict(os.environ, {
                    "SEARCH_REDUCTION_INDEX": str(self.directory / "index"),
                    "SEARCH_REDUCTION_SOURCE_LIBRARY": str(self.directory / "library")},
                    clear=True), patch.object(cache, "__file__", str(
                        self.directory / "tools/scripts/search-reduction-probe-cache.py")):
                baseline = cache.input_identity("request.lean", root, self.key)
                for name in files:
                    with self.subTest(input=name):
                        path = Path(name)
                        stamp = path.stat()
                        path.write_bytes(b"other")
                        os.utime(path, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
                        changed = cache.input_identity("request.lean", root, self.key)
                        self.assertNotEqual(baseline, changed)
                        path.write_bytes(b"first")
                        self.assertEqual(baseline, cache.input_identity(
                            "request.lean", root, self.key))
                Path("index/new-page.json").write_bytes(b"new")
                self.assertNotEqual(baseline, cache.input_identity("request.lean", root, self.key))
        finally:
            os.chdir(before_cwd)

    def make_record(self):
        path = self.directory / "record"
        path.mkdir()
        (path / "probe.pickle").write_bytes(b"typed probe")
        (path / "Evidence.olean").write_bytes(b"checked dependency module")
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        cache.valid_record(path, "input", self.key)
        return path

    def test_corrupt_typed_record_is_rejected(self):
        path = self.make_record()
        (path / "probe.pickle").write_bytes(b"different!!")
        with self.assertRaises(ValueError):
            cache.valid_record(path, "input", self.key)

    def test_tampered_dependency_module_is_rejected(self):
        path = self.make_record()
        (path / "Evidence.olean").write_bytes(b"forged module")
        with self.assertRaises(ValueError):
            cache.valid_record(path, "input", self.key)

    def test_recomputed_checksum_cannot_authenticate_a_forgery(self):
        path = self.make_record()
        (path / "probe.pickle").write_bytes(b"forged probe")
        manifest = json.loads((path / "manifest.json").read_text())
        manifest["data"]["files"] = cache.record_files(path)
        (path / "manifest.json").write_text(json.dumps(manifest))
        with self.assertRaises(ValueError):
            cache.valid_record(path, "input", self.key)

    def test_corruption_recomputes_cold_and_preserves_failure(self):
        path = self.make_record()
        (path / "probe.pickle").write_bytes(b"broken")
        # Exercise the production orchestration, with a failed cold compiler.
        # A corrupt cache must not turn that failure into a successful verdict.
        root = self.directory
        path.rename(root / "input")
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(root)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", return_value="input"), \
                patch.object(cache.subprocess, "call", return_value=23) as compiler:
            self.assertEqual(cache.run(["lean", "request.lean"]), 23)
            self.assertEqual(compiler.call_count, 1)
            environment = compiler.call_args.kwargs["env"]
            self.assertNotIn("SEARCH_REDUCTION_PROBE_READ", environment)
            self.assertIn("SEARCH_REDUCTION_PROBE_WRITE", environment)


if __name__ == "__main__":
    unittest.main()
