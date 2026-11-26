"""Incremental Truth Release reader fixtures."""

import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace
import tarfile
import tempfile
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("reader", Path(__file__).with_name("read-module-reports.py"))
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def archive(path, files):
    with tarfile.open(path, "w:gz") as tar:
        for name, data in files.items():
            entry = tarfile.TarInfo("./" + name if name in reader.BUNDLE_FILES else name)
            entry.size = len(data)
            tar.addfile(entry, io.BytesIO(data))


def module(name, key):
    return {"key": key, "report_inputs": [name], "compiler_input": "compiler-" + name}


class ReportReaderTest(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.schema = "fixture-raw-report-current"
        self.canonical = lambda value: (json.dumps(value, sort_keys=True) + "\n").encode()
        self.enterContext(patch.dict(sys.modules, materials=SimpleNamespace(
            REPORT_SCHEMA=self.schema, canonical_json=self.canonical)))
        self.source = "b" * 40
        self.current = "lean-modules-" + self.source
        self.old = "lean-modules-" + "a" * 40
        self.tag = "truth-release-" + "f" * 64
        self.release = {"tagName": self.tag, "tagCommit": {"oid": "a" * 40}}
        self.base = self.root / "truth-base"
        self.destination = self.root / "reports"
        for tag in (self.current, self.old, self.tag):
            (self.root / tag).mkdir()
        self.index = {
            "schema": "lean-module-shards-v1", "mathlib": "mathlib",
            "targets": {n: module(n, n) for n in ["Same", "Changed", "Added", "Moved"]},
            "shards": {
                "mixed": {"version": self.current, "asset": "mixed.tar.gz", "members": ["Same", "Changed"]},
                "added": {"version": self.old, "asset": "added.tar.gz", "members": ["Moved", "Added"]},
                "compiler": {"version": self.current, "asset": "absent.tar.gz", "members": ["Compiler"]},
            },
        }
        self.index["targets"]["Compiler"] = {"key": "compiler", "compiler_input": "compiler"}
        old = {**self.index, "targets": {n: module(n, n) for n in ["Same", "Changed", "Removed", "Moved"]}}
        old["targets"]["Changed"]["key"] = "different-utility-closure"
        self.write_index(self.current, self.index)
        self.write_index(self.old, old)
        for row in self.index["shards"].values():
            if row["members"] != ["Compiler"]:
                archive(self.root / row["version"] / row["asset"],
                        {"lean-inspector/modules/" + n + ".zip": n.encode() for n in row["members"]})
        coordinate = json.dumps({"release_digest": "sha256:" + "f" * 64, "source_commit": "a" * 40}).encode()
        (self.root / self.tag / reader.PUBLICATION).write_bytes(coordinate)
        files = dict.fromkeys(reader.BUNDLE_FILES, b"bundle-data")
        self.files = files
        files["raw-lean-report.json"] = self.canonical({"modules": [], "schema": self.schema})
        files[reader.PUBLICATION] = coordinate
        archive(self.root / self.tag / (self.tag + ".tar.gz"), files)

    def write_index(self, tag, index):
        (self.root / tag / "index.json").write_text(json.dumps(index))

    def read(self, release):
        with patch.object(reader, "download", wraps=reader.download) as requests:
            existing = reader.read_reports(self.root.as_uri(), self.current, self.destination,
                                           base_directory=self.base, previous=release)
        return existing, [(c.args[1], c.args[2]) for c in requests.call_args_list]

    def test_mixed_shards_and_removed_reports(self):
        _, calls = self.read(self.release)
        self.assertEqual(json.loads((self.base / "reuse.json").read_text()), ["Moved", "Same"])
        self.assertEqual({p.name for p in self.base.iterdir()}, reader.BUNDLE_FILES | {"reuse.json"})
        self.assertEqual({p.name for p in self.destination.iterdir()}, {"Changed.zip", "Added.zip"})
        self.assertEqual([asset for tag, asset in calls if asset.endswith(".tar.gz") and tag != self.tag],
                         ["mixed.tar.gz", "added.tar.gz"])

    def test_all_keys_reused_in_new_source(self):
        self.write_index(self.old, self.index)
        _, calls = self.read(self.release)
        self.assertEqual(json.loads((self.base / "reuse.json").read_text()), ["Added", "Changed", "Moved", "Same"])
        self.assertFalse(list(self.destination.iterdir()))
        self.assertFalse(any(asset.endswith(".tar.gz") and tag != self.tag for tag, asset in calls))

    def test_same_source_needs_no_download(self):
        release = {**self.release, "tagCommit": {"oid": self.source}}
        existing, calls = self.read(release)
        self.assertEqual(existing, self.tag)
        self.assertEqual(calls, [])
        self.assertFalse(self.destination.exists())

    def test_first_publication(self):
        _, calls = self.read(None)
        self.assertFalse(self.base.exists())
        self.assertEqual(len(list(self.destination.glob("*.zip"))), 4)
        self.assertNotIn((self.current, "absent.tar.gz"), calls)

    def test_incompatible_mathlib_uses_current_reports(self):
        self.write_index(self.old, {**self.index, "mathlib": "before-toolchain-update"})
        _, calls = self.read(self.release)
        self.assertEqual(len(list(self.destination.glob("*.zip"))), 4)
        self.assertFalse(self.base.exists())
        self.assertNotIn((self.tag, self.tag + ".tar.gz"), calls)

    def test_older_raw_format_uses_current_zips_even_with_equal_keys(self):
        self.write_index(self.old, self.index)
        self.files["raw-lean-report.json"] = self.canonical({"modules": [], "schema": "previous-format"})
        archive(self.root / self.tag / (self.tag + ".tar.gz"), self.files)
        self.read(self.release)
        self.assertFalse(self.base.exists())
        self.assertEqual({p.name for p in self.destination.iterdir()}, {"Added.zip", "Same.zip", "Changed.zip", "Moved.zip"})

    def test_recognizes_only_the_canonical_envelope_without_reading_the_body(self):
        class Observed(io.BytesIO):
            def read(stream, size=-1):
                self.assertLess(size, 100)
                self.assertGreater(size, 0)
                return super().read(size)
        empty = self.canonical({"modules": [], "schema": self.schema})
        fixture = self.root / "raw-lean-report.json"
        with patch.object(Path, "open", return_value=Observed(empty.replace(b"[]", b"[" + b" " * 50000 + b"]"))):
            self.assertTrue(reader.compatible_report(fixture))
        for incompatible in (empty.rstrip(), b" " + empty, b'{"modules": ['):
            with self.subTest(incompatible=incompatible):
                fixture.write_bytes(incompatible)
                self.assertFalse(reader.compatible_report(fixture))

    def test_missing_required_bundle_member_uses_current_zip_files(self):
        archive(self.root / self.tag / (self.tag + ".tar.gz"), {"SHA256SUMS": b"legacy"})
        self.read(self.release)
        self.assertFalse(self.base.exists())
        self.assertEqual(len(list(self.destination.glob("*.zip"))), 4)

    def test_all_inputs_changed_still_provides_compatible_base_files(self):
        changed = {name: module(name, "changed-" + name) for name in self.index["targets"]}
        self.write_index(self.old, {**self.index, "targets": changed})
        self.read(self.release)
        self.assertEqual(json.loads((self.base / "reuse.json").read_text()), [])
        self.assertTrue((self.base / "truth-graph.v1.json").is_file())
        self.assertEqual(len(list(self.destination.glob("*.zip"))), 4)

    def test_missing_old_index_cold_start(self):
        download = reader.download

        def missing_index(base, version, asset, destination, *, optional=False):
            if version == self.old and asset == "index.json" and optional:
                return False
            return download(base, version, asset, destination, optional=optional)

        with patch.object(reader, "download", side_effect=missing_index):
            self.read(self.release)
        self.assertFalse(self.base.exists())
        self.assertEqual(len(list(self.destination.glob("*.zip"))), 4)

    def test_failed_download_is_not_a_missing_index(self):
        for status, expected in (("404", False), ("503", subprocess.CalledProcessError)):
            with self.subTest(status=status), patch.object(reader.subprocess, "run",
                    return_value=subprocess.CompletedProcess([], 22, stdout=status)):
                if expected is False:
                    self.assertFalse(reader.download("https://example.org", self.old, "index.json", self.base, optional=True))
                else:
                    with self.assertRaises(expected):
                        reader.download("https://example.org", self.old, "index.json", self.base, optional=True)

    def test_selects_latest_published_ancestor_across_pages(self):
        def release(sha, day, **values):
            return {"tagName": "truth-release-" + sha * 64, "tagCommit": {"oid": sha * 40},
                    "isDraft": False, "isPrerelease": False, "publishedAt": day, **values}
        unrelated = release("b", "2")
        expected = release("a", "1")
        pages = [{"data": {"repository": {"releases": {"nodes": nodes}}}} for nodes in (
            [release("e", "5", isDraft=True), release("f", "6", isPrerelease=True)],
            [release("c", "4", tagName="other"), unrelated, expected],
        )]
        with patch.object(reader.subprocess, "check_output", side_effect=[json.dumps(pages), "other", "a" * 40]):
            self.assertEqual(reader.select_release("owner/repo", "d" * 40), expected)


if __name__ == "__main__":
    unittest.main()
