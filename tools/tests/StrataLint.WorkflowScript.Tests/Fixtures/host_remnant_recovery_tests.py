"""Path-specific retained-history recovery and bounded fallback contracts."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
from unittest.mock import patch

import host_reclaim_tests as fixtures

cleanup, ROOT = fixtures.cleanup, fixtures.ROOT


class RemnantRecoveryTests(unittest.TestCase):
    setUp = fixtures.HostReclaimTests.setUp
    git = fixtures.HostReclaimTests.git
    age = fixtures.HostReclaimTests.age
    remnant = fixtures.HostReclaimTests.remnant
    clean_remnant = fixtures.HostReclaimTests.clean_remnant

    def mixed_history(self, common_count=100, missing_count=3):
        """Most bytes match a named tip; the rest survive only in another tip's old history."""
        target = self.remnant("matching", blueprint=False)
        blueprint = self.main / "Blueprint"
        blueprint.mkdir()
        for index in range(common_count):
            (blueprint / ("Common%05d.md" % index)).write_text("common %d\n" % index)
        self.git(self.main, "add", "Blueprint")
        self.git(self.main, "commit", "-m", "Common blueprint")
        matching = self.git(self.main, "rev-parse", "HEAD")
        self.git(self.main, "branch", "lane/math/matching")
        for index in range(missing_count):
            (blueprint / ("Old [*] %03d\t.md" % index)).write_text("historical %d\n" % index)
        self.git(self.main, "add", "Blueprint")
        self.git(self.main, "commit", "-m", "Historical blueprint")
        historical = self.git(self.main, "rev-parse", "HEAD")
        shutil.copytree(blueprint, target / "Blueprint")
        for path in blueprint.glob("Old*"):
            path.write_text("different tip bytes\n")
        self.git(self.main, "commit", "-am", "Replace historical bytes")
        tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        archive = self.git(self.main, "rev-parse", "HEAD")
        for index in range(40):
            archive = self.git(self.main, "commit-tree", tree, "-p", archive, "-m", "Later %d" % index)
        self.git(self.main, "update-ref", "refs/heads/z-archive", archive)
        self.git(self.main, "reset", "--hard", matching)
        tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        for index in range(17):
            tip = self.git(self.main, "commit-tree", tree, "-p", matching, "-m", "Other %d" % index)
            self.git(self.main, "update-ref", "refs/heads/a-other-%02d" % index, tip)
        self.age(target)
        return target, historical, archive

    def observed_git(self, calls, on_log=None):
        preservation, _ = cleanup.worktree_modules()
        git = preservation.git
        def observed(root, *arguments, **options):
            self.assertNotIn("--objects", arguments, "[FAIL] no_reachable_object_enumeration")
            self.assertNotIn("--batch-all-objects", arguments, "[FAIL] no_reachable_object_enumeration")
            calls.append((arguments, options))
            if "log" in arguments and on_log:
                return on_log(root, arguments, options, git)
            return git(root, *arguments, **options)
        return patch.object(preservation, "git", side_effect=observed)

    def test_recovery_requires_the_same_path_in_sample_and_history(self):
        target = self.remnant(blueprint=False)
        (target / "Blueprint").mkdir()
        (target / "Blueprint/Unique.md").write_text("same blob at another path\n")
        (self.main / "Blueprint").mkdir()
        (self.main / "Blueprint/Other.md").write_text("same blob at another path\n")
        self.git(self.main, "add", "Blueprint")
        self.git(self.main, "commit", "-m", "Retain other path")
        self.age(target)
        for historical in (False, True):
            with self.subTest(historical=historical):
                if historical:
                    self.git(self.main, "rm", "Blueprint/Other.md")
                    self.git(self.main, "commit", "-m", "Remove other path")
                result = self.clean_remnant(target, delete=False)
                self.assertEqual(("kept", "blueprint_unrecoverable"),
                                 (result["action"], result["reason"]), "[FAIL] recovery_same_path: " + str(result))
        self.assertTrue(target.exists())

    def test_recovery_excludes_dangling_reflog_blob_and_tree_roots(self):
        target = self.remnant()
        retained = self.git(self.main, "rev-parse", "HEAD")
        blob = self.git(self.main, "rev-parse", "HEAD:Blueprint/Retained.md")
        tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        self.git(self.main, "reset", "--hard", "HEAD~1")
        self.git(self.main, "update-ref", "refs/tags/blob-only", blob)
        self.git(self.main, "update-ref", "refs/tags/tree-only", tree)
        self.assertIn(retained, self.git(self.main, "reflog", "--format=%H"))
        for state in ("reflog-only", "dangling"):
            with self.subTest(state=state):
                if state == "dangling":
                    self.git(self.main, "reflog", "expire", "--expire=all", "--all")
                calls = []
                with self.observed_git(calls):
                    result = self.clean_remnant(target, delete=False)
                self.assertEqual(("kept", "blueprint_unrecoverable"),
                                 (result["action"], result["reason"]), result)
                logs = [(arguments, options) for arguments, options in calls if "log" in arguments]
                self.assertEqual(1, len(logs), "[FAIL] retained_history_lookup_is_exercised")
                arguments, options = logs[0]
                self.assertNotIn("--all", arguments)
                self.assertNotIn("--reflog", arguments)
                self.assertNotIn(retained.encode(), options["input"])
        self.assertTrue(target.exists())

    def test_recovery_lookup_count_overflow_is_named_and_keeps_bytes(self):
        target, _, _ = self.mixed_history(missing_count=3)
        calls = []
        with patch.object(cleanup.RefRecovery, "HISTORY_LOOKUP_LIMIT", 2, create=True), \
             self.observed_git(calls):
            result = self.clean_remnant(target)
        self.assertEqual(("kept", "recovery_search_limit"), (result["action"], result["reason"]), result)
        self.assertIn("lookup_count", result["detail"])
        self.assertFalse(any("log" in arguments for arguments, _ in calls))
        self.assertEqual(103, len(list((target / "Blueprint").iterdir())))

    def test_recovery_lookup_timeout_is_named_and_keeps_bytes(self):
        target, _, _ = self.mixed_history()
        def timeout(root, arguments, options, git):
            self.assertGreater(options["timeout"], 0)
            self.assertLessEqual(options["timeout"], cleanup.RefRecovery.HISTORY_LOOKUP_SECONDS)
            raise subprocess.TimeoutExpired(arguments, options["timeout"])
        with self.observed_git([], timeout):
            result = self.clean_remnant(target)
        self.assertEqual(("kept", "recovery_search_limit"), (result["action"], result["reason"]), result)
        self.assertIn("timeout", result["detail"])
        self.assertTrue(target.exists())

    def test_recovery_total_deadline_stops_before_another_lookup(self):
        target, _, _ = self.mixed_history()
        elapsed = [0]
        def advance(root, arguments, options, git):
            result = git(root, *arguments, **options)
            elapsed[0] = 121
            return result
        calls = []
        with patch.object(cleanup.time, "monotonic", side_effect=lambda: elapsed[0]), \
             self.observed_git(calls, advance):
            result = self.clean_remnant(target)
        self.assertEqual(("kept", "recovery_search_limit"), (result["action"], result["reason"]), result)
        self.assertIn("deadline", result["detail"])
        self.assertEqual(1, sum("log" in arguments for arguments, _ in calls))
        self.assertTrue(target.exists())

    def test_recovery_lookup_failure_and_malformed_evidence_fail_closed(self):
        target, _, _ = self.mixed_history()
        for failure in ("git", "malformed"):
            def broken(root, arguments, options, git):
                if failure == "git":
                    raise subprocess.CalledProcessError(128, arguments, stderr=b"unreadable history")
                return subprocess.CompletedProcess(arguments, 0, b"invalid raw diff\0", b"")
            with self.subTest(failure=failure), self.observed_git([], broken):
                result = self.clean_remnant(target)
            self.assertEqual(("kept", "recovery_unverifiable"), (result["action"], result["reason"]), result)
        self.assertTrue(target.exists())

    def test_recovery_mixed_history_outside_tip_and_commit_samples(self):
        target, historical, archive = self.mixed_history()
        recovery = cleanup.RefRecovery(self.main)
        self.addCleanup(recovery.close)
        calls = []
        with self.observed_git(calls):
            result = self.clean_remnant(target, delete=False, recovery=recovery)
        self.assertNotIn(archive.encode(), recovery.selected_roots())
        self.assertNotIn(historical.encode(), recovery.scanned)
        self.assertEqual("would_remove", result["action"], "[FAIL] recovery_beyond_samples: " + str(result))
        logs = [(arguments, options) for arguments, options in calls if "log" in arguments]
        self.assertEqual(3, len(logs))
        for arguments, options in logs:
            self.assertIn("--max-count=1", arguments)
            self.assertIn("--literal-pathspecs", arguments)
            self.assertIn(archive.encode(), options["input"])
        self.assertTrue(target.exists())

    def test_recovery_cached_path_evidence_is_cleared_when_refs_change(self):
        target, _, archive = self.mixed_history()
        recovery = cleanup.RefRecovery(self.main)
        self.addCleanup(recovery.close)
        calls = []
        with self.observed_git(calls):
            self.assertEqual("would_remove", self.clean_remnant(target, delete=False, recovery=recovery)["action"])
            calls.clear()
            peer = target.with_name(target.name + "-peer")
            shutil.copytree(target, peer)
            self.age(peer)
            self.assertEqual("would_remove", self.clean_remnant(peer, delete=False, recovery=recovery)["action"])
        self.assertFalse(any("log" in arguments for arguments, _ in calls))
        self.git(self.main, "update-ref", "-d", "refs/heads/z-archive", archive)
        result = self.clean_remnant(target, delete=False, recovery=recovery)
        self.assertEqual(("kept", "blueprint_unrecoverable"), (result["action"], result["reason"]), result)

    def test_recovery_ref_change_during_fallback_cannot_authorize_deletion(self):
        target, _, archive = self.mixed_history()
        changed = False
        def moving(root, arguments, options, git):
            nonlocal changed
            result = git(root, *arguments, **options)
            if not changed:
                self.git(self.main, "update-ref", "-d", "refs/heads/z-archive", archive)
                changed = True
            return result
        with self.observed_git([], moving):
            result = self.clean_remnant(target)
        self.assertEqual(("kept", "recovery_unverifiable"), (result["action"], result["reason"]), result)
        self.assertIn("recovery_refs_changed", result["detail"])
        self.assertTrue(target.exists())


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["RemnantRecoveryTests." + name
                          for name in unittest.defaultTestLoader.getTestCaseNames(RemnantRecoveryTests)]))
    else:
        unittest.main()
