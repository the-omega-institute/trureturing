#!/usr/bin/env python3
"""Regression checks for input binding and authenticated cache corruption."""
import importlib.util
import json
import os
import re
import subprocess
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

    def test_wall_phases_use_a_system_clock_across_exec(self):
        path = self.directory / "wall.log"
        with patch.dict(os.environ, {"SEARCH_REDUCTION_PROFILE": str(path)}), \
                patch.object(cache.time, "clock_gettime_ns", return_value=1234567), \
                patch.object(cache.time, "monotonic_ns", side_effect=AssertionError(
                    "Python 3.9 Darwin monotonic epochs are process-local")):
            cache.wall_phase("test")
        self.assertEqual(path.read_text(), "WALL 1234567 test\n")

    def test_unchanged_inventory_does_not_rewrite_the_signed_memo(self):
        root = self.directory / "cache"
        root.mkdir()
        request = self.directory / "request.lean"
        request.write_text("first")
        before_cwd = Path.cwd()
        try:
            os.chdir(self.directory)
            with patch.dict(os.environ, {}, clear=True):
                before = cache.input_identity(request, root, self.key)
                with patch.object(cache, "write_signed", wraps=cache.write_signed) as writer, \
                        patch.object(cache, "digest", wraps=cache.digest) as hasher:
                    self.assertEqual(before, cache.input_identity(request, root, self.key))
        finally:
            os.chdir(before_cwd)
        writer.assert_not_called()
        hasher.assert_not_called()

    def test_inventory_reads_each_file_stat_once(self):
        tree = self.directory / "input"
        tree.mkdir()
        member = tree / "source.olean"
        member.write_bytes(b"source")
        import stat
        ordinary_stat = cache.os.stat
        reads = []

        def counted(path, *args, **kwargs):
            info = ordinary_stat(path, *args, **kwargs)
            if stat.S_ISREG(info.st_mode):
                reads.append(str(path))
            return info

        with patch.object(cache.os, "stat", side_effect=counted), \
                patch.object(cache.Path, "stat", new=counted):
            cache.tree_fingerprint(tree, {}, {})
        self.assertEqual(reads, [str(member)])

    def test_hot_tree_reuses_aggregate_only_after_complete_stamp_scan(self):
        tree = self.directory / "input"
        tree.mkdir()
        members = [tree / f"source-{i}.olean" for i in range(3)]
        for member in members:
            member.write_bytes(b"source")
        memo, trees = {}, {}
        first = cache.tree_fingerprint(tree, {}, memo, tree_memo={}, trees=trees)
        updated, next_trees = {}, {}
        ordinary_stat, ordinary_canonical = cache.os.stat, cache.canonical
        reads, leaf_encodings = [], []

        def counted(path, *args, **kwargs):
            reads.append(str(path))
            return ordinary_stat(path, *args, **kwargs)

        def encoded(value):
            if isinstance(value, list) and len(value) == 2:
                leaf_encodings.append(value)
            return ordinary_canonical(value)

        with patch.object(cache.os, "stat", side_effect=counted), \
                patch.object(cache, "canonical", side_effect=encoded):
            self.assertEqual(first, cache.tree_fingerprint(
                tree, memo, updated, tree_memo=trees, trees=next_trees))
        self.assertEqual(set(reads), {str(tree), *(str(p) for p in members)})
        self.assertEqual(len(reads), 4)
        self.assertEqual(leaf_encodings, [])
        self.assertEqual(memo, updated)
        self.assertEqual(trees, next_trees)
        added = tree / "added.olean"
        added.write_bytes(b"new population member")
        self.assertNotEqual(first, cache.tree_fingerprint(
            tree, memo, {}, tree_memo=trees, trees={}))
        members[0].write_bytes(b"changed source")
        new_memo = {}
        changed = cache.tree_fingerprint(tree, memo, new_memo)
        self.assertNotEqual(first, changed)
        # A crash between publishing the file memo and the aggregate memo
        # must not authorize an old aggregate against current file hashes.
        self.assertEqual(changed, cache.tree_fingerprint(
            tree, new_memo, {}, tree_memo=trees, trees={}))

    def test_hot_identity_avoids_per_member_serialization(self):
        root = self.directory / "cache"
        root.mkdir()
        request = self.directory / "request.lean"
        request.write_text("request")
        source = self.directory / "D5/Target.lean"
        source.parent.mkdir()
        source.write_text("target")
        ordinary_canonical = cache.canonical
        encoded_leaves = []

        def encoded(value):
            if isinstance(value, list) and len(value) == 2:
                encoded_leaves.append(value)
            return ordinary_canonical(value)

        before_cwd = Path.cwd()
        try:
            os.chdir(self.directory)
            with patch.dict(os.environ, {}, clear=True):
                first = cache.input_identity(request, root, self.key)
                with patch.object(cache, "canonical", side_effect=encoded):
                    self.assertEqual(first, cache.input_identity(request, root, self.key))
        finally:
            os.chdir(before_cwd)
        self.assertEqual(encoded_leaves, [])

    def test_selected_source_file_reads_its_stamp_once(self):
        source = self.directory / "Target.olean"
        source.write_bytes(b"source")
        ordinary_stat = cache.os.stat
        reads = []

        def counted(path, *args, **kwargs):
            if str(path) == str(source):
                reads.append(str(path))
            return ordinary_stat(path, *args, **kwargs)

        with patch.object(cache.os, "stat", side_effect=counted), \
                patch.object(cache.Path, "stat", new=counted):
            cache.source_data_fingerprints([str(source)], self.directory, self.key)
        self.assertEqual(reads, [str(source)])

    def test_each_semantic_input_invalidates_old_result(self):
        files = ["request.lean", "D5/Target.lean", "Golden/Frozen/state/Target.json",
                 "index/page.json", "library/Source.olean", "lake-manifest.json",
                 "lean-toolchain", ".lake/packages/mathlib/Mathlib.lean",
                 ".lake/packages/mathlib/lake-manifest.json"]
        programs = ["Makefile", "tools/lean-inspector/Judge.lean",
                    "tools/lean-inspector-interface/Contract.lean", "Reg/Registration.lean",
                    "tools/lean-inspector-reg/lakefile.lean",
                    "tools/scripts/search-reduction-runner.sh",
                    "tools/scripts/search-reduction-probe-cache.py",
                    ".lake/build/lean-inspector/reg/lib/Judge.olean",
                    ".lake/build/lean-inspector/interface/lib/Contract.olean",
                    ".lake/build/lean-inspector/producer/lib/Producer.olean"]
        for name in files + programs:
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
                for name in programs:
                    with self.subTest(program=name):
                        Path(name).write_bytes(b"changed program")
                        self.assertEqual(baseline, cache.input_identity(
                            "request.lean", root, self.key))
                for version in ["VERSION", "R_VERSION"]:
                    with self.subTest(version=version), patch.object(cache, version, "other"):
                        self.assertNotEqual(baseline, cache.input_identity(
                            "request.lean", root, self.key))
                with patch.dict(os.environ, {"SEARCH_REDUCTION_MEMO": "0"}):
                    self.assertNotEqual(baseline, cache.input_identity(
                        "request.lean", root, self.key))
                Path("index/new-page.json").write_bytes(b"new")
                self.assertNotEqual(baseline, cache.input_identity("request.lean", root, self.key))
        finally:
            os.chdir(before_cwd)

    def test_explicit_r_version_matches_current_lean_configuration(self):
        sources = Path("tools/lean-inspector/LeanInformationAuditRegAnalysis/SearchReduction")
        lookup = re.search(r'abbrev lookupVersion : String := "([^"]+)"',
                           (sources / "Lookup.lean").read_text()).group(1)
        local = re.search(r'abbrev localConfiguration : String := lookupVersion \+\+ "([^"]+)"',
                          (sources / "Local.lean").read_text()).group(1)
        self.assertEqual(cache.R_VERSION, lookup + local)
        commands = (sources / "Commands.lean").read_text()
        status = re.search(r'abbrev probeRejectionExit : UInt32 := (\d+)', commands)
        self.assertEqual(cache.REJECTION_EXIT, int(status.group(1)))
        self.assertIn('"probe-record-v11"', commands)
        self.assertEqual(cache.VERSION, "probe-cache-v11")

    def cold_terminal(self, status):
        """Model only the Lean transport, never inspect diagnostic contents."""
        calls = []

        def compiler(command, env=None):
            calls.append(dict(env or {}))
            if "SEARCH_REDUCTION_PROBE_WRITE" in env:
                stage = Path(env["SEARCH_REDUCTION_PROBE_WRITE"])
                (stage / "probe.pickle").write_bytes(b"typed terminal")
                (stage / "entry-plan").write_bytes(b"probe\n")
                (stage / "entry-probe.lean").write_text("checked entry")
                (stage / "entry-probe.olean").write_bytes(b"request payload")
                cache.write_signed(stage / "source-data.json", {}, self.key)
                # Diagnostics can say anything; the exit status is the typed
                # Lean protocol, and the runner must never parse these bytes.
                (stage / "diagnostics.txt").write_text("timeout source_certificate_leak")
            return status

        return calls, compiler

    def test_typed_rejection_is_stored_and_replayed_with_the_same_nonzero_exit(self):
        calls, compiler = self.cold_terminal(cache.REJECTION_EXIT)
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", return_value="input"), \
                patch.object(cache.subprocess, "call", side_effect=compiler):
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)
            cache.valid_record(self.directory / "input", "input", self.key)
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)
        self.assertEqual(len(calls), 2)
        self.assertIn("SEARCH_REDUCTION_PROBE_WRITE", calls[0])
        self.assertIn("SEARCH_REDUCTION_PROBE_READ", calls[1])
        self.assertNotIn("SEARCH_REDUCTION_PROBE_WRITE", calls[1])

    def test_faults_never_sign_even_a_partially_written_typed_record(self):
        for status in [1, 2, 23, 75, 124, 137, -9, -15]:
            with self.subTest(status=status):
                calls, compiler = self.cold_terminal(status)
                with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                            "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                        patch.object(cache, "auth_key", return_value=self.key), \
                        patch.object(cache, "input_identity", return_value="input"), \
                        patch.object(cache.subprocess, "call", side_effect=compiler):
                    self.assertEqual(cache.run(["lean", "request.lean"]), status)
                    self.assertEqual(cache.run(["lean", "request.lean"]), status)
                self.assertEqual(len(calls), 2)
                self.assertTrue(all("SEARCH_REDUCTION_PROBE_WRITE" in c for c in calls))
                self.assertFalse((self.directory / "input").exists())

    def test_rejection_rechecks_identity_before_signing(self):
        calls, compiler = self.cold_terminal(cache.REJECTION_EXIT)
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", side_effect=["input", "changed"]), \
                patch.object(cache.subprocess, "call", side_effect=compiler):
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)
        self.assertFalse((self.directory / "input").exists())

    def test_rejected_cache_tampering_forces_cold_without_upgrading_rejection(self):
        calls, compiler = self.cold_terminal(cache.REJECTION_EXIT)
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", return_value="input"), \
                patch.object(cache.subprocess, "call", side_effect=compiler):
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)
            (self.directory / "input/probe.pickle").write_bytes(b"forged rejection")
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)
        self.assertTrue(all("SEARCH_REDUCTION_PROBE_WRITE" in c for c in calls))

    def test_disabled_cache_keeps_the_rejection_nonzero(self):
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": "0"}), \
                patch.object(cache.subprocess, "call", return_value=cache.REJECTION_EXIT):
            self.assertEqual(cache.run(["lean", "request.lean"]), 1)

    def test_real_lean_terminal_preserves_the_rejection_diagnostic(self):
        built = subprocess.run([
            "make", "lean", "LEAN_SKIP_LOCK=1",
            "LEAN_TARGETS=LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture"],
            text=True, capture_output=True)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        request = self.directory / "terminal.lean"
        request.write_text('''import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction
run_cmd withCacheFixture fun f => do
  let request := {f.request with additions := #[`cacheFixtureAux]}
  let result := {f.result with graph? := some {
    graph := {edges := [{conclusion := 0, zeroProof := some (mkConst `cacheFixtureAux)}]} }}
  f.write result (some {arm := .baseline, dependency := `cacheFixtureAux})
  discard <| replayProbeCache f.directory f.identity request #[] `terminalTransportRegression
''')
        profile = self.directory / "terminal.profile"
        env = dict(os.environ, SEARCH_REDUCTION_PROBE_CACHE="0",
                   SEARCH_REDUCTION_WORKERS="1", SEARCH_REDUCTION_RESUME="",
                   SEARCH_REDUCTION_PROFILE=str(profile))
        result = subprocess.run(["make", "search-reduction-run", f"REQUESTS={request}"],
                                env=env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("baseline: search.source_certificate_leak:cacheFixtureAux", result.stderr)
        self.assertIn("PROBE_CACHE hit=authenticated", result.stderr)
        trace = profile.read_text()
        self.assertNotIn("R_QUERY", trace)
        self.assertNotIn("search/branch/start", trace)

    def make_record(self):
        path = self.directory / "record"
        path.mkdir()
        (path / "probe.pickle").write_bytes(b"typed probe")
        (path / "Evidence.olean").write_bytes(b"checked dependency module")
        cache.write_signed(path / "source-data.json", {}, self.key)
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        cache.valid_record(path, "input", self.key)
        return path

    def test_current_mathematical_data_changes_reject_an_authenticated_record(self):
        path = self.make_record()
        source = self.directory / "Target.olean"
        source.write_bytes(b"current mathematical data")
        absent_part = self.directory / "Target.olean.private"
        inputs = cache.source_data_fingerprints(
            [str(source), str(absent_part)], self.directory, self.key)
        cache.write_signed(path / "source-data.json", inputs, self.key)
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        cache.valid_record(path, "input", self.key)
        (self.directory / "Judge.olean").write_bytes(b"changed current program")
        cache.valid_record(path, "input", self.key)
        source.write_bytes(b"changed mathematical data")
        with self.assertRaisesRegex(ValueError, "mathematical input data changed"):
            cache.valid_record(path, "input", self.key)
        source.write_bytes(b"current mathematical data")
        cache.valid_record(path, "input", self.key)
        absent_part.write_bytes(b"new private declarations")
        with self.assertRaisesRegex(ValueError, "mathematical input data changed"):
            cache.valid_record(path, "input", self.key)

    def test_data_changed_during_cold_computation_cannot_be_resigned(self):
        path = self.make_record()
        source = self.directory / "Target.olean"
        source.write_bytes(b"initial mathematical data")
        (path / "source-input-files.json").write_text(json.dumps([str(source)]))
        with patch.object(cache, "auth_key", return_value=self.key):
            cache.snapshot_source_data(path)
            source.write_bytes(b"changed mathematical data")
            with self.assertRaisesRegex(ValueError, "mathematical input data changed"):
                cache.snapshot_source_data(path)

    def test_source_data_inventory_authentication_is_required(self):
        path = self.make_record()
        (path / "source-data.json").write_text('{"data":{},"mac":"forged"}')
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        with self.assertRaisesRegex(ValueError, "authentication failed"):
            cache.valid_record(path, "input", self.key)

    def test_authenticated_entry_skips_wrapper_and_kernel_failure_replays_original(self):
        path = self.make_record()
        (path / "entry-plan").write_bytes(b"probe\n")
        (path / "entry-probe.lean").write_text("live Lean replay entry")
        (path / "entry-probe.olean").write_bytes(b"typed request")
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        path.rename(self.directory / "input")
        path = self.directory / "input"
        commands, environments = [], []

        def compile_request(command, env):
            commands.append(command)
            environments.append(dict(env))
            return 1 if len(commands) == 1 else 23

        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", return_value="input"), \
                patch.object(cache.subprocess, "call", side_effect=compile_request):
            self.assertEqual(cache.run(["lean", "request.lean"]), 23)
        self.assertEqual(commands, [["lean", str(path / "entry-probe.lean")],
                                    ["lean", "request.lean"]])
        self.assertEqual(environments[0]["LEAN_PATH"].split(os.pathsep)[0], str(path))
        self.assertNotEqual(environments[1].get("LEAN_PATH", "").split(os.pathsep)[0], str(path))
        self.assertIn("SEARCH_REDUCTION_PROBE_READ", environments[0])
        self.assertNotIn("SEARCH_REDUCTION_PROBE_READ", environments[1])
        self.assertIn("SEARCH_REDUCTION_PROBE_WRITE", environments[1])

    def test_partial_or_multiple_probe_entries_keep_original_wrapper(self):
        path = self.make_record()
        entry = path / "entry-probe.lean"
        entry.write_text("entry")
        (path / "entry-plan").write_bytes(b"probe\n")
        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean"}):
            command = ["lean", "request.lean"]
            self.assertEqual(cache.replay_command(command, path), command)
            entry.with_suffix(".olean").write_bytes(b"request")
            self.assertNotEqual(cache.replay_command(command, path), command)
            (path / "entry-plan").write_bytes(b"probe\nprobe\n")
            self.assertEqual(cache.replay_command(command, path), command)
            (path / "entry-plan").write_bytes(b"probe\n")
            (path / "second.pickle").write_bytes(b"second probe")
            self.assertEqual(cache.replay_command(command, path), command)

    def test_corrupt_replay_entry_is_rejected(self):
        path = self.make_record()
        entry = path / "entry-probe.lean"
        entry.write_text("entry")
        cache.write_signed(path / "manifest.json",
                           {"identity": "input", "files": cache.record_files(path)}, self.key)
        entry.write_text("tampered")
        with self.assertRaises(ValueError):
            cache.valid_record(path, "input", self.key)

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

    def test_kernel_rejection_recomputes_cold_and_preserves_failure(self):
        path = self.make_record()
        path.rename(self.directory / "input")
        environments = []

        def compile_request(command, env):
            environments.append(dict(env))
            return 1 if len(environments) == 1 else 23

        with patch.dict(os.environ, {"SEARCH_REDUCTION_REQUESTS": "request.lean",
                                    "SEARCH_REDUCTION_PROBE_CACHE": str(self.directory)}), \
                patch.object(cache, "auth_key", return_value=self.key), \
                patch.object(cache, "input_identity", return_value="input"), \
                patch.object(cache.subprocess, "call", side_effect=compile_request) as compiler:
            self.assertEqual(cache.run(["lean", "request.lean"]), 23)
            self.assertEqual(compiler.call_count, 2)
            hot, cold = environments
            self.assertIn("SEARCH_REDUCTION_PROBE_READ", hot)
            self.assertNotIn("SEARCH_REDUCTION_PROBE_WRITE", hot)
            self.assertNotIn("SEARCH_REDUCTION_PROBE_READ", cold)
            self.assertIn("SEARCH_REDUCTION_PROBE_WRITE", cold)

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
