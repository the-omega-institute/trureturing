"""Behavior checks for host cleanup and the worktree disk preflight."""

import importlib.util
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SCRIPT = Path(sys.argv.pop(1)).resolve()
spec = importlib.util.spec_from_file_location("host_cleanup", SCRIPT)
cleanup = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cleanup
spec.loader.exec_module(cleanup)


class HostCleanupTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix="host cleanup test ")
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name)
        self.cutoff = time.time() - 3600

    def old_file(self, path):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("artifact")
        os.utime(path, (self.cutoff - 10, self.cutoff - 10))
        return path

    def test_strict_five_percent_boundary(self):
        for free, allowed in ((499, False), (500, True), (501, True)):
            with self.subTest(free=free), patch.object(
                cleanup.shutil, "disk_usage", return_value=shutil._ntuple_diskusage(10000, 10000-free, free)
            ):
                if allowed:
                    cleanup.check_disk([self.root])
                else:
                    with self.assertRaises(cleanup.LowDiskSpace):
                        cleanup.check_disk([self.root])

    def test_destination_uses_nearest_existing_parent(self):
        with patch.object(cleanup.shutil, "disk_usage", return_value=shutil._ntuple_diskusage(100, 94, 6)) as usage:
            cleanup.check_disk([self.root / "missing" / "worktree"])
        usage.assert_called_once_with(self.root)
        self.assertFalse((self.root / "missing").exists())

    def test_explicit_override_allows_low_space_but_not_unreadable_usage(self):
        with patch.object(cleanup.shutil, "disk_usage", return_value=shutil._ntuple_diskusage(100, 99, 1)):
            self.assertTrue(cleanup.check_disk([self.root], allow_low_disk=True)[0]["overridden"])
        with patch.object(cleanup.shutil, "disk_usage", side_effect=OSError("unreadable")):
            with self.assertRaises(OSError):
                cleanup.check_disk([self.root], allow_low_disk=True)

    def test_dry_run_and_delete_have_distinct_effects(self):
        artifact = self.old_file(self.root / "old-output")
        dry = cleanup.clean_candidate(artifact, self.cutoff, [], delete=False)
        self.assertEqual("would_remove", dry["action"])
        self.assertTrue(artifact.exists())
        deleted = cleanup.clean_candidate(artifact, self.cutoff, [], delete=True)
        self.assertEqual("removed", deleted["action"])
        self.assertFalse(artifact.exists())

    def test_recent_descendant_keeps_old_parent(self):
        artifact = self.old_file(self.root / "old-dir" / "old")
        artifact.with_name("running").write_text("new")
        os.utime(artifact.parent, (self.cutoff - 10, self.cutoff - 10))
        result = cleanup.clean_candidate(artifact.parent, self.cutoff, [], delete=True)
        self.assertEqual("recent", result["reason"])
        self.assertTrue(artifact.exists())

    def test_active_path_keeps_entire_candidate(self):
        artifact = self.old_file(self.root / "flight" / "worker.log")
        os.utime(artifact.parent, (self.cutoff - 10, self.cutoff - 10))
        result = cleanup.clean_candidate(artifact.parent, self.cutoff, [artifact], delete=True)
        self.assertEqual("protected", result["reason"])
        self.assertTrue(artifact.exists())

    def test_symlink_does_not_delete_its_target(self):
        target = self.old_file(self.root / "target")
        link = self.root / "link"
        link.symlink_to(target)
        result = cleanup.clean_candidate(link, self.cutoff, [], delete=True)
        self.assertEqual("symlink", result["reason"])
        self.assertTrue(target.exists())

    def test_unregistered_repository_is_preserved(self):
        artifact = self.old_file(self.root / "repository" / ".git")
        os.utime(artifact.parent, (self.cutoff - 10, self.cutoff - 10))
        result = cleanup.clean_candidate(artifact.parent, self.cutoff, [], delete=True)
        self.assertEqual("repository", result["reason"])
        self.assertTrue(artifact.exists())

    def test_changed_candidate_is_not_removed(self):
        artifact = self.old_file(self.root / "old-output")
        inspect = cleanup.inspect_candidate
        calls = 0
        def changed(*args):
            nonlocal calls
            calls += 1
            if calls == 2:
                artifact.write_text("active write")
            return inspect(*args)
        with patch.object(cleanup, "inspect_candidate", side_effect=changed):
            result = cleanup.clean_candidate(artifact, self.cutoff, [], delete=True)
        self.assertEqual("changed", result["reason"])
        self.assertTrue(artifact.exists())

    def test_product_inventory_excludes_settings_skills_and_runtime_databases(self):
        codex = self.root / "codex"
        sshx = self.root / "sshx"
        tmp = self.root / "tmp"
        paths = [
            codex / "sessions/2026/01/01/rollout-test.jsonl",
            codex / "archived_sessions/rollout-test.jsonl",
            codex / "shell_snapshots/test.sh",
            codex / "tmp/arg0/codex-arg0test/output",
            codex / "log/codex-tui.log",
            sshx / ("a" * 24) / "attempt-1/status.json",
            tmp / "arbitrary-output",
        ]
        for path in paths:
            self.old_file(path)
        for name in ("auth.json", "config.toml", "state.sqlite", "skills/skill.md"):
            self.old_file(codex / name)
        inventory = list(cleanup.candidates(codex, sshx, [tmp]))
        selected = [str(path) for _, path in inventory]
        self.assertEqual(7, len(selected))
        self.assertFalse(any(name in str(selected) for name in ("auth.json", "config.toml", "state.sqlite", "skill.md")))

    def test_clean_lanes_failure_is_propagated(self):
        with patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 2)) as run:
            self.assertEqual(2, cleanup.clean_worktrees(self.root, "base", True))
        self.assertIn("--lanes-only", run.call_args.args[0])
        self.assertIn("--force", run.call_args.args[0])

    def test_invalid_age_is_rejected(self):
        for age in ("-1", "nan", "inf"):
            result = subprocess.run([sys.executable, str(SCRIPT), "clean", "--min-age-hours", age], capture_output=True)
            self.assertNotEqual(0, result.returncode)

    def test_files_under_an_active_filesystem_root_are_still_eligible(self):
        artifact = self.old_file(self.root / "old-output")
        self.assertEqual("would_remove", cleanup.clean_candidate(artifact, self.cutoff, [Path("/")])["action"])

    def test_failure_in_worktree_cleanup_does_not_hide_artifact_results(self):
        artifact = self.old_file(self.root / "tmp" / "old-output")
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"],
            min_age_hours=1, delete=True, verbose=False)
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", return_value=set()), \
             patch.object(cleanup, "registered_worktrees", return_value={self.root / "checkout"}), \
             patch.object(cleanup, "clean_worktrees", return_value=2), contextlib.redirect_stdout(output):
            self.assertEqual(1, cleanup.run_clean(options))
        self.assertFalse(artifact.exists())
        summary = json.loads(output.getvalue().splitlines()[-1])
        self.assertEqual("failed", summary["status"])
        self.assertEqual(2, summary["worktree_exit"])

    def test_missing_active_file_inspection_refuses_cleanup(self):
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"],
            min_age_hours=1, delete=True, verbose=False)
        with patch.object(cleanup, "active_paths", side_effect=OSError("probe unavailable")), \
             patch.object(cleanup, "registered_worktrees", return_value=set()), \
             patch.object(cleanup, "clean_worktrees") as lanes:
            with self.assertRaises(OSError):
                cleanup.run_clean(options)
        lanes.assert_not_called()

    def test_worktree_make_blocks_before_dotnet_and_forwards_explicit_override(self):
        repository = self.root / "checkout with spaces"
        scripts = repository / "tools/scripts"
        scripts.mkdir(parents=True)
        shutil.copy(SCRIPT, scripts / SCRIPT.name)
        shutil.copy(SCRIPT.with_name("worktree-init.sh"), scripts / "worktree-init.sh")
        shutil.copy(SCRIPT.parents[2] / "Makefile", repository / "Makefile")
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        python = bin_dir / "python3"
        python.write_text(
            "#!" + sys.executable + "\nimport os,runpy,shutil,sys\n"
            "free=int(os.environ['TEST_DISK_FREE'])\n"
            "shutil.disk_usage=lambda path: shutil._ntuple_diskusage(100,100-free,free)\n"
            "args=sys.argv[1:]\n"
            "if args[0]=='-B': args.pop(0)\n"
            "sys.argv=args\nrunpy.run_path(args[0],run_name='__main__')\n")
        dotnet = bin_dir / "dotnet"
        dotnet.write_text("#!/bin/sh\nprintf 'DOTNET_INVOKED\\n'\n")
        python.chmod(0o700)
        dotnet.chmod(0o700)
        env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"], TEST_DISK_FREE="4")
        arguments = ["make", "-C", str(repository), "worktree", "KIND=governance", "NAME=test", "DEST=../new tree"]
        blocked = subprocess.run(arguments, cwd=self.root, env=env, capture_output=True, text=True)
        self.assertNotEqual(0, blocked.returncode)
        self.assertIn("WORKTREE_LOW_DISK", blocked.stderr)
        self.assertNotIn("DOTNET_INVOKED", blocked.stdout)
        self.assertFalse((self.root / "new tree").exists())
        inherited = subprocess.run(arguments, cwd=self.root, env=dict(env, ALLOW_LOW_DISK="1"), capture_output=True, text=True)
        self.assertNotEqual(0, inherited.returncode)
        self.assertNotIn("DOTNET_INVOKED", inherited.stdout)
        allowed = subprocess.run(arguments + ["ALLOW_LOW_DISK=1"], cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(0, allowed.returncode, allowed.stderr)
        self.assertIn("DOTNET_INVOKED", allowed.stdout)
        exact = subprocess.run(arguments, cwd=self.root, env=dict(env, TEST_DISK_FREE="5"), capture_output=True, text=True)
        self.assertEqual(0, exact.returncode, exact.stderr)
        invalid = subprocess.run(arguments + ["ALLOW_LOW_DISK=2"], cwd=self.root, env=env, capture_output=True, text=True)
        self.assertNotEqual(0, invalid.returncode)
        self.assertNotIn("DOTNET_INVOKED", invalid.stdout)

    def test_cleanup_make_forwards_paths_flags_and_literal_shell_characters(self):
        repository = self.root / "checkout with spaces"
        scripts = repository / "tools/scripts"
        scripts.mkdir(parents=True)
        shutil.copy(SCRIPT.parents[1] / "Makefile", repository / "tools/Makefile")
        (scripts / SCRIPT.name).write_text("import json,sys\nprint(json.dumps(sys.argv[1:]))\n")
        literal = str(self.root / "tmp `touch SENTINEL` $(touch SENTINEL2)")
        arguments = ["make", "--no-print-directory", "-C", str(repository / "tools"), "clean-all",
                     "CLEAN_TMP_ROOT=" + literal, "CLEAN_CODEX_HOME=" + str(self.root / "codex home"),
                     "CLEAN_SSHX_HOME=" + str(self.root / "sshx home"), "FORCE=1", "VERBOSE=1"]
        result = subprocess.run(arguments, cwd=self.root, capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        forwarded = json.loads(result.stdout)
        self.assertIn(literal, forwarded)
        self.assertIn("--delete", forwarded)
        self.assertIn("--verbose", forwarded)
        self.assertFalse((repository / "tools/SENTINEL").exists())
        self.assertFalse((repository / "tools/SENTINEL2").exists())
        default = subprocess.run(["make", "--no-print-directory", "-C", str(repository / "tools"), "clean-all"],
                                 cwd=self.root, capture_output=True, text=True)
        self.assertEqual(0, default.returncode, default.stderr)
        self.assertNotIn("--delete", json.loads(default.stdout))

    def test_help_renders_percent_as_plain_text(self):
        result = subprocess.run([sys.executable, str(SCRIPT), "--help"], capture_output=True, text=True)
        self.assertEqual(0, result.returncode)
        self.assertIn("5% available disk space", result.stdout)

    def test_inventory_failure_reports_already_removed_artifacts(self):
        artifact = self.old_file(self.root / "tmp" / "old-output")
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"],
            min_age_hours=1, delete=True, verbose=False)
        def interrupted_inventory(*args):
            yield "tmp", artifact
            raise OSError("inventory unavailable")
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", return_value=set()), \
             patch.object(cleanup, "registered_worktrees", return_value=set()), \
             patch.object(cleanup, "clean_worktrees", return_value=0), \
             patch.object(cleanup, "candidates", side_effect=interrupted_inventory), \
             contextlib.redirect_stdout(output):
            self.assertEqual(1, cleanup.run_clean(options))
        summary = json.loads(output.getvalue().splitlines()[-1])
        self.assertEqual("inventory unavailable", summary["inventory_error"])
        self.assertEqual(1, summary["counts"]["tmp:removed"])

    def test_unreadable_candidate_is_retained_and_counted(self):
        artifact = self.old_file(self.root / "old-output")
        with patch.object(cleanup, "inspect_candidate", side_effect=PermissionError("access denied")):
            result = cleanup.clean_candidate(artifact, self.cutoff, [], delete=True)
        self.assertEqual("kept", result["action"])
        self.assertEqual("unreadable", result["reason"])
        self.assertTrue(artifact.exists())

    def test_delete_permission_failure_is_still_a_failure(self):
        artifact = self.old_file(self.root / "old-output")
        with patch.object(Path, "unlink", side_effect=PermissionError("delete denied")):
            result = cleanup.clean_candidate(artifact, self.cutoff, [], delete=True)
        self.assertEqual("failed", result["action"])
        self.assertTrue(artifact.exists())


if __name__ == "__main__":
    unittest.main()
