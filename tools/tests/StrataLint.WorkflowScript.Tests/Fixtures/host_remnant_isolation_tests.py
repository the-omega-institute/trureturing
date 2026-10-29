"""Atomic remnant isolation and ordinary concurrent writer contracts."""

import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import host_reclaim_tests as fixtures

cleanup, ROOT = fixtures.cleanup, fixtures.ROOT


class RemnantIsolationTests(unittest.TestCase):
    setUp = fixtures.HostReclaimTests.setUp
    git = fixtures.HostReclaimTests.git
    age = fixtures.HostReclaimTests.age
    remnant = fixtures.HostReclaimTests.remnant
    clean_remnant = fixtures.HostReclaimTests.clean_remnant

    def isolated(self, target):
        paths = list(target.parent.glob(target.name + "-cleanup-*"))
        self.assertEqual(1, len(paths), paths)
        return paths[0]

    def writer_race(self, trigger, hold=False):
        target = self.remnant()
        relative = "Blueprint/Retained.md"
        if trigger == "scan":
            for name in ("A.md", "Z.md"):
                (self.main / "Blueprint" / name).write_bytes(b"retained blueprint\n")
                (target / "Blueprint" / name).write_bytes(b"retained blueprint\n")
            self.git(self.main, "add", "Blueprint")
            self.git(self.main, "commit", "-m", "Retain scan fixtures")
            self.age(target)
            relative = "Blueprint/Z.md"
        unique = b"unique ordinary buffered save\n"
        program = """
import os, pathlib, sys
print('ready', flush=True)
sys.stdin.readline()
try:
    handle = open(sys.argv[1], 'r+b')
except FileNotFoundError:
    print('blocked', flush=True)
else:
    print('opened', flush=True)
    sys.stdin.readline()
    handle.seek(0)
    handle.write(%r)
    handle.truncate()
    handle.flush()
    os.fsync(handle.fileno())
    handle.close()
    print('saved', flush=True)
""" % unique
        environment = dict(os.environ, CLEAN_TMP_ROOT=str(self.root / "tmp"),
                           CODEX_HOME=str(self.root / "codex"), SSHX_HOME=str(self.root / "sshx"))
        process = subprocess.Popen([sys.executable, "-u", "-c", program,
                                    str((target / relative).relative_to(self.root))], cwd=self.root,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=environment)
        self.addCleanup(lambda: process.communicate(timeout=10))
        self.assertEqual(b"ready\n", process.stdout.readline())
        run, open_file = subprocess.run, Path.open
        reads, attempted, outcome = 0, False, None
        def save():
            nonlocal attempted, outcome
            attempted = True
            process.stdin.write(b"open\n")
            process.stdin.flush()
            outcome = process.stdout.readline()
            if outcome == b"opened\n" and not hold:
                process.stdin.write(b"save\n")
                process.stdin.flush()
                self.assertEqual(b"saved\n", process.stdout.readline())
        def raced_run(arguments, **kwargs):
            nonlocal reads
            result = run(arguments, **kwargs)
            if arguments[-2:] == ["cat-file", "--batch"]:
                reads += 1
                if reads == 2 and trigger == "recovery":
                    save()
            return result
        def raced_open(path, *args, **kwargs):
            if trigger == "scan" and reads == 2 and path.name == "A.md" and not attempted:
                save()
            return open_file(path, *args, **kwargs)
        def activity():
            siblings = [target, *target.parent.glob(target.name + "-cleanup-*")]
            return fixtures.fixture_active_paths(self.root / "codex", [process.pid], scopes=siblings)
        with patch.object(cleanup.subprocess, "run", side_effect=raced_run), \
             patch.object(Path, "open", raced_open):
            result = self.clean_remnant(target, activity=activity)
        if hold and outcome == b"opened\n":
            process.stdin.write(b"save\n")
            process.stdin.flush()
            self.assertEqual(b"saved\n", process.stdout.readline())
        process.communicate(timeout=10)
        self.assertTrue(attempted, result)
        if outcome == b"opened\n":
            self.assertTrue(target.exists(), "ordinary writer bytes were unlinked: " + str(result))
            self.assertEqual(unique, (target / relative).read_bytes())
        self.assertEqual(b"blocked\n", outcome, result)
        self.assertEqual("removed", result["action"], result)

    def test_save_during_recovery_cannot_reopen_original_path(self):
        self.writer_race("recovery")

    def test_open_held_during_recovery_cannot_lose_buffered_save(self):
        self.writer_race("recovery", hold=True)

    def test_save_to_already_scanned_file_cannot_reopen_original_path(self):
        self.writer_race("scan")

    def test_preexisting_open_handle_and_cwd_survive_isolation(self):
        for kind in ("open", "cwd"):
            with self.subTest(kind=kind):
                target = self.remnant(kind)
                relative = "Blueprint/Retained.md"
                program = """
import os, sys
handle = open(sys.argv[1], 'r+b') if sys.argv[2] == 'open' else None
if handle is None:
    os.chdir(os.path.dirname(sys.argv[1]))
print('ready', flush=True)
sys.stdin.readline()
if handle is None:
    handle = open('Retained.md', 'wb')
handle.write(b'unique saved through retained handle')
handle.flush()
os.fsync(handle.fileno())
handle.close()
"""
                process = None
                def activity():
                    nonlocal process
                    pids = [process.pid] if process is not None else [os.getpid()]
                    observed = fixtures.fixture_active_paths(self.root / "codex", pids, scopes=[self.root])
                    if process is None:
                        process = subprocess.Popen([sys.executable, "-u", "-c", program,
                                                    str((target / relative).relative_to(self.root)), kind], cwd=self.root,
                                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE)
                        self.assertEqual(b"ready\n", process.stdout.readline())
                    return observed
                try:
                    result = self.clean_remnant(target, activity=activity)
                    process.communicate(b"save\n", timeout=10)
                    self.assertEqual("kept", result["action"], result)
                    self.assertIn(b'unique saved through retained handle', (target / relative).read_bytes())
                finally:
                    if process is not None and process.poll() is None:
                        process.communicate(timeout=10)

    def test_post_isolation_failures_restore_original_name(self):
        for failure in ("activity", "recovery", "scan", "remove"):
            with self.subTest(failure=failure):
                target = self.remnant(failure)
                inspect, check, remove = cleanup.inspect_candidate, cleanup.RefRecovery.check, cleanup.remove_tree
                observed = False
                def activity():
                    nonlocal observed
                    if not target.exists():
                        observed = True
                        self.isolated(target)
                        if failure == "activity":
                            raise OSError("activity_unobservable")
                    return set()
                def recovery(reader, wanted):
                    if not target.exists() and failure == "recovery":
                        raise ValueError("recovery_refs_changed")
                    return check(reader, wanted)
                def scan(path, *args, **kwargs):
                    if not target.exists() and failure == "scan":
                        raise PermissionError("unreadable remnant")
                    return inspect(path, *args, **kwargs)
                def remove_candidate(path):
                    if failure == "remove":
                        raise OSError("removal_unavailable")
                    return remove(path)
                with patch.object(cleanup.RefRecovery, "check", recovery), \
                     patch.object(cleanup, "inspect_candidate", side_effect=scan), \
                     patch.object(cleanup, "remove_tree", side_effect=remove_candidate):
                    result = self.clean_remnant(target, activity=activity)
                self.assertTrue(observed, result)
                self.assertNotEqual("removed", result["action"], result)
                self.assertTrue(target.exists(), result)
                self.assertEqual(b"retained blueprint\x00bytes\n", (target / "Blueprint/Retained.md").read_bytes())
                self.assertEqual([], list(target.parent.glob(target.name + "-cleanup-*")))

    def test_occupied_restore_destination_preserves_both_names(self):
        for occupant in ("empty", "file", "directory", "symlink"):
            with self.subTest(occupant=occupant):
                target = self.remnant(occupant)
                def activity():
                    if target.exists():
                        return set()
                    isolated = self.isolated(target)
                    if occupant in ("empty", "directory"):
                        target.mkdir()
                        if occupant == "directory":
                            (target / "unique").write_bytes(b"new original occupant")
                    elif occupant == "file":
                        target.write_bytes(b"new original occupant")
                    else:
                        target.symlink_to(self.main, target_is_directory=True)
                    return {isolated}
                result = self.clean_remnant(target, activity=activity)
                isolated = self.isolated(target)
                self.assertEqual(("kept", "restore_destination_exists"),
                                 (result["action"], result["reason"]), result)
                self.assertEqual(str(isolated), result["retained_path"], result)
                self.assertTrue(os.path.lexists(target))
                self.assertEqual(b"retained blueprint\x00bytes\n", (isolated / "Blueprint/Retained.md").read_bytes())
                if occupant == "file":
                    self.assertEqual(b"new original occupant", target.read_bytes())
                if occupant == "directory":
                    self.assertEqual(b"new original occupant", (target / "unique").read_bytes())
                if occupant == "symlink":
                    self.assertTrue(target.is_symlink())

    def test_killed_after_rename_is_rediscovered_and_requalified(self):
        target = self.remnant()
        program = """
import importlib.util, pathlib, sys
spec = importlib.util.spec_from_file_location('cleanup', sys.argv[1])
cleanup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cleanup)
target, repository = map(pathlib.Path, sys.argv[2:4])
def activity():
    if not target.exists():
        print('isolated', flush=True)
        sys.stdin.read()
    return set()
cleanup.clean_candidate(target, float(sys.argv[4]), [], delete=True,
                        repository=repository, remnant=True, activity=activity)
print('finished without isolation', flush=True)
"""
        environment = dict(os.environ, CLEAN_TMP_ROOT=str(self.root / "tmp"),
                           CODEX_HOME=str(self.root / "codex"), SSHX_HOME=str(self.root / "sshx"))
        process = subprocess.Popen([sys.executable, "-B", "-u", "-c", program,
                                    str(ROOT / "tools/scripts/host-cleanup.py"), str(target),
                                    str(self.main), str(self.cutoff)], cwd=self.root,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=environment)
        try:
            self.assertEqual(b"isolated\n", process.stdout.readline())
            process.kill()
            process.communicate(timeout=10)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate(timeout=10)
        isolated = self.isolated(target)
        self.assertFalse(target.exists())
        self.assertIn(isolated, list(cleanup.remnant_candidates(self.main, [self.main])))
        self.assertEqual("would_remove", self.clean_remnant(isolated, delete=False)["action"])
        (isolated / "Blueprint/Retained.md").write_bytes(b"unique post-crash content")
        retained = self.clean_remnant(isolated)
        self.assertEqual(("kept", "recent"), (retained["action"], retained["reason"]), retained)
        (isolated / "Blueprint/Retained.md").write_bytes(b"retained blueprint\x00bytes\n")
        self.age(isolated)
        self.assertEqual("removed", self.clean_remnant(isolated)["action"])
        self.assertFalse(isolated.exists())


    def unrelated_tips(self, count, tree):
        for index in range(count):
            commit = self.git(self.main, "commit-tree", tree, "-m", "Unrelated tip " + str(index))
            self.git(self.main, "update-ref", "refs/heads/a-unrelated-" + str(index), commit)

    def bounded_recovery_calls(self, calls):
        popen = subprocess.Popen
        def observed(arguments, **kwargs):
            if arguments[0] == "git":
                self.assertNotIn("--objects", arguments, "[FAIL] bounded_recovery_no_object_walk")
                self.assertNotIn("--batch-all-objects", arguments, "[FAIL] bounded_recovery_no_object_walk")
                calls.append(arguments)
                if "rev-list" in arguments:
                    self.assertIn("--max-count=32", arguments, "[FAIL] bounded_recovery_history_sample")
            return popen(arguments, **kwargs)
        return patch.object(cleanup.subprocess, "Popen", side_effect=observed)

    def test_recovery_matching_tip_ignores_unrelated_object_history(self):
        baseline = self.git(self.main, "rev-parse", "HEAD")
        baseline_tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        for count, suffix in ((0, ""), (48, "-cleanup-" + "a" * 32 + "-cleanup-" + "b" * 32)):
            with self.subTest(unrelated_tips=count):
                target = self.remnant("matching" + suffix)
                retained = self.git(self.main, "rev-parse", "HEAD")
                self.git(self.main, "update-ref", "refs/heads/lane/math/matching", retained)
                self.git(self.main, "reset", "--hard", baseline)
                self.unrelated_tips(count, baseline_tree)
                calls = []
                with self.bounded_recovery_calls(calls):
                    result = self.clean_remnant(target, delete=False)
                self.assertEqual("would_remove", result["action"], result)
                trees = [call for call in calls if "ls-tree" in call]
                self.assertEqual(1, len(trees), "[FAIL] matching_tip_tree_reads")
                self.assertIn(retained, trees[0])
                self.assertFalse(any("rev-list" in call for call in calls),
                                 "[FAIL] matching_tip_needs_no_history")
                self.assertEqual(1, sum(call[-2:] == ["cat-file", "--batch"] for call in calls))

    def test_recovery_unsampled_history_keeps_bytes_with_bounded_tree_reads(self):
        target = self.remnant()
        retained = self.git(self.main, "rev-parse", "HEAD")
        self.git(self.main, "rm", "Blueprint/Retained.md")
        self.git(self.main, "commit", "-m", "Remove blueprint from tip")
        tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        tip = self.git(self.main, "rev-parse", "HEAD")
        for index in range(40):
            tip = self.git(self.main, "commit-tree", tree, "-p", tip, "-m", "Later history " + str(index))
        self.git(self.main, "update-ref", "refs/heads/dev", tip)
        self.assertEqual(retained, self.git(self.main, "rev-parse", "HEAD~41"))
        calls = []
        with self.bounded_recovery_calls(calls):
            result = self.clean_remnant(target, delete=False)
        self.assertEqual(("kept", "blueprint_unrecoverable"), (result["action"], result["reason"]), result)
        self.assertLessEqual(sum("ls-tree" in call for call in calls), 48,
                             "[FAIL] bounded_recovery_tree_reads")
        self.assertTrue((target / "Blueprint/Retained.md").exists())

    def test_recovery_sampled_parent_is_recoverable_without_a_tip_copy(self):
        target = self.remnant()
        self.git(self.main, "rm", "Blueprint/Retained.md")
        self.git(self.main, "commit", "-m", "Remove tip blueprint")
        calls = []
        with self.bounded_recovery_calls(calls):
            result = self.clean_remnant(target, delete=False)
        self.assertEqual("would_remove", result["action"], result)
        self.assertTrue(any("rev-list" in call for call in calls))

    def test_recovery_matching_name_cannot_certify_unique_bytes(self):
        target = self.remnant("matching")
        self.git(self.main, "branch", "lane/math/matching")
        (target / "Blueprint/Retained.md").write_bytes(b"unique bytes despite matching ref name")
        self.age(target)
        result = self.clean_remnant(target, delete=False)
        self.assertEqual(("kept", "blueprint_unrecoverable"), (result["action"], result["reason"]), result)

    def test_recovery_annotated_commit_tag_qualifies_but_tree_ref_does_not(self):
        target = self.remnant("tagged")
        baseline = self.git(self.main, "rev-parse", "HEAD~1")
        tree = self.git(self.main, "rev-parse", "HEAD^{tree}")
        self.git(self.main, "tag", "-a", "tagged", "-m", "Retained commit tag")
        self.git(self.main, "reset", "--hard", baseline)
        self.assertEqual("would_remove", self.clean_remnant(target, delete=False)["action"])
        self.git(self.main, "tag", "-d", "tagged")
        self.git(self.main, "update-ref", "refs/tags/tagged-tree", tree)
        result = self.clean_remnant(target, delete=False)
        self.assertEqual(("kept", "blueprint_unrecoverable"), (result["action"], result["reason"]), result)


if __name__ == "__main__":
    if sys.argv[1:] == ["--list-tests"]:
        print(json.dumps(["RemnantIsolationTests." + name
                          for name in unittest.defaultTestLoader.getTestCaseNames(RemnantIsolationTests)]))
    else:
        unittest.main()
