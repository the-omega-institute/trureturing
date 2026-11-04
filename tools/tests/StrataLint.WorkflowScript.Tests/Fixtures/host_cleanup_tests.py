"""Behavior checks for host cleanup and the worktree disk preflight."""

import importlib.util
import contextlib
import io
import json
import os
import select
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import types
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
        self.root = Path(self.workspace.name).resolve()
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

    def test_aggregate_cleanup_applies_ordinary_artifact_policy(self):
        tmp = self.root / "tmp"
        ordinary = self.old_file(tmp / "ordinary" / "arbitrary-output")
        os.utime(ordinary.parent, (self.cutoff - 10, self.cutoff - 10))
        regular = self.old_file(tmp / "regular")
        repository = self.old_file(tmp / "repository" / ".git")
        os.utime(repository.parent, (self.cutoff - 10, self.cutoff - 10))
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[tmp],
            min_age_hours=1, delete=False, verbose=True)
        with patch.object(cleanup, "active_paths", return_value=set()), \
             patch.object(cleanup, "registered_worktrees", return_value=set()), \
             patch.object(cleanup, "clean_worktrees", return_value=0):
            for delete in (False, True):
                options.delete = delete
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    self.assertEqual(0, cleanup.run_clean(options))
                rows = [json.loads(line) for line in output.getvalue().splitlines()]
                actions = {row["path"]: row["action"] for row in rows if "path" in row}
                for path in (ordinary.parent, regular, repository.parent):
                    self.assertEqual("removed" if delete else "would_remove", actions[str(path)])
                    self.assertEqual(not delete, path.exists())

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

    def test_codex_repository_is_preserved(self):
        artifact = self.old_file(self.root / "repository" / ".git")
        os.utime(artifact.parent, (self.cutoff - 10, self.cutoff - 10))
        result = cleanup.clean_candidate(artifact.parent, self.cutoff, [], delete=True, reclaim=False)
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

    def test_codex_inventory_selects_only_superseded_package_releases(self):
        codex = self.root / "codex"
        packages = codex / "packages"
        for package in ("standalone", "app-server-daemon", "dangling", "outside", "plain"):
            for version in ("0.1", "0.2", "0.3"):
                self.old_file(packages / package / "releases" / version / "bin" / "codex")
            self.old_file(packages / package / "auto-update-version")
        os.symlink("releases/0.3", packages / "standalone" / "current")
        (packages / "app-server-daemon" / "current").symlink_to(packages / "app-server-daemon" / "releases" / "0.2")
        os.symlink("releases/9.9", packages / "dangling" / "current")
        (packages / "outside" / "current").symlink_to(self.root)
        target = self.root / "linked target"
        for version in ("0.1", "0.2"):
            self.old_file(target / "releases" / version / "bin" / "codex")
        os.symlink("releases/0.2", target / "current")
        (packages / "linked").symlink_to(target, target_is_directory=True)
        inventory = {path for category, path in cleanup.candidates(codex, self.root / "sshx", [])
                     if category == "codex"}
        expected = {packages / "standalone" / "releases" / "0.1", packages / "standalone" / "releases" / "0.2",
                    packages / "app-server-daemon" / "releases" / "0.1",
                    packages / "app-server-daemon" / "releases" / "0.3"}
        self.assertEqual(expected, inventory, "[FAIL] codex_superseded_releases_selected")

    def test_inventory_error_callback_continues_after_symlinked_artifact_root(self):
        codex, sshx, temporary = (self.root / name for name in ("codex", "sshx", "tmp"))
        outside = self.old_file(self.root / "outside" / "rollout-private.jsonl")
        (codex / "sessions").parent.mkdir(parents=True)
        (codex / "sessions").symlink_to(outside.parent, target_is_directory=True)
        archived = self.old_file(codex / "archived_sessions" / "rollout-old.jsonl")
        flight = self.old_file(sshx / ("a" * 24) / "output")
        artifact = self.old_file(temporary / "old-output")
        errors = []
        inventory = list(cleanup.candidates(codex, sshx, [temporary],
                                           on_error=lambda *error: errors.append(error)))
        self.assertEqual({archived, flight.parent, artifact}, {path for _, path in inventory})
        self.assertEqual(1, len(errors))
        self.assertEqual(("codex", codex / "sessions"), errors[0][:2])
        self.assertIsInstance(errors[0][2], OSError)
        with self.assertRaises(OSError):
            list(cleanup.candidates(codex, sshx, [temporary]))

    def test_inventory_error_callback_continues_after_unreadable_package(self):
        codex, sshx = self.root / "codex", self.root / "sshx"
        packages = codex / "packages"
        bad, good = packages / "bad", packages / "good"
        for package in (bad, good):
            for version in ("old", "current"):
                self.old_file(package / "releases" / version / "bin" / "codex")
            (package / "current").symlink_to("releases/current", target_is_directory=True)
        flight = self.old_file(sshx / ("a" * 24) / "output")
        children = cleanup.children
        def unreadable(root):
            if root == bad / "releases":
                raise PermissionError("package unavailable")
            yield from children(root)
        errors = []
        with patch.object(cleanup, "children", side_effect=unreadable):
            inventory = list(cleanup.candidates(codex, sshx, [],
                                               on_error=lambda *error: errors.append(error)))
        self.assertEqual({good / "releases" / "old", flight.parent}, {path for _, path in inventory})
        self.assertEqual(1, len(errors))
        self.assertEqual("codex", errors[0][0])
        self.assertTrue(errors[0][1] == bad or bad in errors[0][1].parents)
        self.assertIsInstance(errors[0][2], PermissionError)

    def test_inventory_error_reports_failure_and_continues_independent_cleanup(self):
        codex, temporary = self.root / "codex", self.root / "tmp"
        outside = self.old_file(self.root / "outside" / "rollout-private.jsonl")
        codex.mkdir()
        (codex / "sessions").symlink_to(outside.parent, target_is_directory=True)
        artifact = self.old_file(temporary / "old-output")
        options = cleanup.argparse.Namespace(repository=self.root, base="base", codex_home=codex,
            sshx_home=self.root / "sshx", tmp_root=[temporary], min_age_hours=1,
            delete=True, verbose=False)
        output, warning = io.StringIO(), io.StringIO()
        with patch.object(cleanup, "active_paths", return_value=set()), \
             patch.object(cleanup, "registered_worktrees", return_value=[]), \
             patch.object(cleanup, "clean_worktrees", return_value=0), \
             contextlib.redirect_stdout(output), contextlib.redirect_stderr(warning):
            self.assertEqual(1, cleanup.run_clean(options))
        summary = json.loads(output.getvalue().splitlines()[-1])
        self.assertEqual("failed", summary["status"])
        self.assertTrue(summary["inventory_error"])
        self.assertEqual(1, summary["counts"]["tmp:removed"])
        self.assertFalse(artifact.exists())
        self.assertTrue(outside.exists())

    def test_clean_lanes_failure_is_propagated(self):
        with patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 2)) as run:
            self.assertEqual(2, cleanup.clean_worktrees(self.root, "base", True))
        self.assertIn("--lanes-only", run.call_args.args[0])
        self.assertIn("--force", run.call_args.args[0])

    def test_clean_lanes_does_not_receive_activity(self):
        with patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(0, cleanup.clean_worktrees(self.root, "base", True, {self.root}))
        self.assertNotIn("--active-paths-file", run.call_args.args[0])

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

    def test_aggregate_temporary_sweep_removes_ordinary_directories(self):
        repository = self.root / "repository"
        repository.mkdir()
        remote = self.root / "remote.git"
        def git(*args):
            return subprocess.run(["git", "-C", str(repository), *map(str, args)],
                                  capture_output=True, text=True, check=True).stdout.strip()
        git("init", "--initial-branch=dev")
        git("config", "user.name", "Cleanup Tests")
        git("config", "user.email", "cleanup@example.invalid")
        (repository / "owned").write_text("retained\n")
        git("add", ".")
        git("commit", "-m", "baseline")
        git("init", "--bare", remote)
        git("remote", "add", "origin", remote)
        git("push", "origin", "dev")
        temporary = self.root / "tmp"
        safe, unknown = temporary / "safe", temporary / "unknown"
        safe.mkdir(parents=True)
        unknown.mkdir()
        (safe / "owned").write_text("retained\n")
        (unknown / "private").write_text("recovery\n")
        for path in (safe, safe / "owned", unknown, unknown / "private"):
            os.utime(path, (self.cutoff - 10, self.cutoff - 10))
        options = cleanup.argparse.Namespace(repository=repository, base="dev",
            codex_home=self.root / "codex", sshx_home=self.root / "sshx", tmp_root=[temporary],
            min_age_hours=0, delete=True, verbose=False)
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", return_value=set()) as activity, \
             patch.object(cleanup.time, "time", return_value=self.cutoff), \
             patch.object(cleanup, "clean_worktrees", return_value=0), contextlib.redirect_stdout(output):
            result = cleanup.run_clean(options)
        self.assertEqual(0, result, output.getvalue())
        self.assertEqual(1, activity.call_count)
        self.assertTrue(all(call.args == (options.codex_home,) for call in activity.call_args_list))
        summary = json.loads(output.getvalue().splitlines()[-1])
        self.assertEqual("succeeded", summary["status"])
        self.assertEqual(0, summary["worktree_exit"])
        self.assertIsNone(summary["inventory_error"])
        self.assertEqual({"tmp:removed": 2}, summary["counts"])
        self.assertFalse(safe.exists())
        self.assertFalse(unknown.exists())

    def test_missing_artifact_inspection_does_not_block_worktree_cleanup(self):
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"],
            min_age_hours=1, delete=True, verbose=False)
        with patch.object(cleanup, "active_paths", side_effect=OSError("probe unavailable")), \
             patch.object(cleanup, "registered_worktrees", return_value=[self.root / "main", self.root]), \
             patch.object(cleanup, "clean_worktrees", return_value=0) as lanes:
            self.assertEqual(1, cleanup.run_clean(options))
        lanes.assert_called_once_with(self.root, "base", True, working_directory=self.root / "main")

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
        dotnet.write_text("#!/bin/sh\nprintf 'DOTNET_INVOKED\\nDISK_CHECK_PENDING=%s\\n' \"${WORKTREE_REQUIRE_DISK_CHECK:-0}\"\n")
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
        implicit = subprocess.run([arg for arg in arguments if not arg.startswith("DEST=")],
                                  cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(0, implicit.returncode, implicit.stderr)
        self.assertIn("DOTNET_INVOKED", implicit.stdout)
        self.assertIn("DISK_CHECK_PENDING=1", implicit.stdout)
        self.assertNotIn("WORKTREE_LOW_DISK", implicit.stderr)
        self.assertIn("DISK_CHECK_PENDING=0", allowed.stdout)
        (self.root / "new tree").mkdir()
        existing = subprocess.run(arguments, cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(0, existing.returncode, existing.stderr)
        self.assertIn("DOTNET_INVOKED", existing.stdout)
        self.assertIn("DISK_CHECK_PENDING=1", existing.stdout)
        self.assertNotIn("WORKTREE_LOW_DISK", existing.stderr)

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

    def test_canonical_bash_wrapper_handles_empty_and_nonempty_active_arguments(self):
        workspace = tempfile.TemporaryDirectory(prefix="clean-lanes-wrapper-")
        self.addCleanup(workspace.cleanup)
        repository = Path(workspace.name) / "checkout"
        scripts = repository / "tools/scripts"
        scripts.mkdir(parents=True)
        shutil.copy(SCRIPT.parents[1] / "Makefile", repository / "tools/Makefile")
        shutil.copy(SCRIPT.with_name("clean-lanes.sh"), scripts / "clean-lanes.sh")
        bin_dir = self.root / "wrapper bin"
        bin_dir.mkdir()
        dotnet = bin_dir / "dotnet"
        dotnet.write_text("#!" + sys.executable + "\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n")
        dotnet.chmod(0o700)
        env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"])
        for force in (False, True):
            result = subprocess.run(
                ["make", "--no-print-directory", "-C", str(repository / "tools"),
                 "clean-lanes", "BASE=HEAD", "FORCE=" + str(int(force))],
                env=env, capture_output=True, text=True)
            self.assertEqual(0, result.returncode, result.stderr)
            args = json.loads(result.stdout)
            self.assertEqual(["clean-lanes", "--base", "HEAD"] + (["--force"] if force else []),
                             args[args.index("--") + 1:])
        activity = str(self.root / "literal $(touch sentinel) `touch other` activity.json")
        result = subprocess.run(
            ["/bin/bash", str(scripts / "clean-lanes.sh"), "--base", "HEAD", "--lanes-only",
             "--active-paths-file", activity],
            cwd=repository, env=env, capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        args = json.loads(result.stdout)
        self.assertEqual(["clean-lanes", "--base", "HEAD", "--lanes-only", "--active-paths-file", activity],
                         args[args.index("--") + 1:])
        self.assertFalse((repository / "sentinel").exists())
        self.assertFalse((repository / "other").exists())
        for rejected in (["--active-path", activity], ["--active-paths-file", activity, "--active-paths-file", activity]):
            with self.subTest(rejected=rejected[0]):
                result = subprocess.run(
                    ["/bin/bash", str(scripts / "clean-lanes.sh"), "--base", "HEAD", *rejected],
                    cwd=repository, env=env, capture_output=True, text=True)
                self.assertEqual(2, result.returncode, "[FAIL] clean_lanes_wrapper_rejects_unsupported_activity")

    def test_physical_kernel_observation_does_not_reopen_endpoint_and_argv_resolves_alias(self):
        target = self.root / "active endpoint"
        target.write_text("owned")
        physical = target.resolve()
        argument_target = self.root / "argument endpoint"
        argument_target.write_text("argv owned")
        argument_physical = argument_target.resolve()
        alias = self.root / "argument-alias"
        alias.symlink_to(argument_physical)
        resolve = Path.resolve

        def inaccessible_endpoint(path, *args, **kwargs):
            if path == physical:
                raise PermissionError("endpoint traversal unavailable")
            return resolve(path, *args, **kwargs)

        def observed(arguments, **kwargs):
            if arguments[0] == "lsof":
                return subprocess.CompletedProcess(arguments, 0, "n" + str(physical) + "\n", "")
            return subprocess.CompletedProcess(arguments, 0,
                str(os.getuid()) + " runner --output=" + json.dumps(str(alias)) + "\n", "")

        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.subprocess, "run", side_effect=observed), \
             patch.object(Path, "resolve", inaccessible_endpoint):
            active = cleanup.active_paths(self.root / "codex")
        self.assertIn(physical, active)
        self.assertIn(argument_physical, active)
        self.assertNotIn(alias, active)

    def test_scoped_activity_preserves_argument_aliases_and_sampler_parent_ownership(self):
        artifact = self.old_file(self.root / "flight" / "output")
        alias = self.root / "argument-alias"
        alias.symlink_to(artifact)
        row = str(os.getuid()) + " " + str(os.getppid()) + " 0 runner --output=" + json.dumps(str(alias)) + "\n"
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup, "macos_active_paths", return_value=set()), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, row, "")):
            ordinary = cleanup.active_paths(self.root / "codex", (artifact,))
            cleanup_activity = cleanup.active_paths(self.root / "codex", (artifact,),
                                                    include_sampler_argv=True)
        self.assertNotIn(artifact, ordinary)
        self.assertIn(artifact, cleanup_activity)
        self.assertNotIn(alias, cleanup_activity)

    def test_scoped_activity_ignores_launcher_arguments_but_keeps_open_paths_and_other_processes(self):
        target = self.old_file(self.root / "target" / "source")
        opened = self.old_file(self.root / "opened" / "source")
        unrelated = self.old_file(self.root / "unrelated" / "source")
        uid = str(os.getuid())
        rows = "\n".join(uid + " " + row for row in (
            "1000 1001 sampler " + json.dumps(str(target)),
            "1001 1002 cli " + json.dumps(str(target)),
            "1002 1 dotnet run --path " + json.dumps(str(target)),
            "1003 1002 worker " + json.dumps(str(unrelated)),
        ))
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.object(cleanup.os, "getpid", return_value=1000), \
             patch.object(cleanup.os, "getppid", return_value=1001), \
             patch.object(cleanup, "macos_active_paths", return_value={opened}), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, rows, "")):
            activity = cleanup.active_paths(self.root / "codex", (self.root,))
            cleanup_activity = cleanup.active_paths(self.root / "codex", (self.root,), include_sampler_argv=True)
        self.assertNotIn(target, activity)
        self.assertIn(opened, activity)
        self.assertIn(unrelated, activity)
        self.assertIn(target, cleanup_activity)

    def test_scoped_activity_keeps_live_lock_identity_without_scanning_other_sessions(self):
        codex = self.root / "codex"
        identity = "active-thread"
        artifact = self.old_file(codex / "sessions" / "rollout-active-thread.jsonl")
        inactive = self.old_file(codex / "sessions" / "rollout-other.jsonl")
        unrelated = self.old_file(codex / "archived_sessions" / "rollout-active-thread.jsonl")
        lock = self.old_file(codex / "thread-writer-locks" / (identity + ".lock"))
        with lock.open("rb") as writer:
            cleanup.fcntl.flock(writer, cleanup.fcntl.LOCK_EX | cleanup.fcntl.LOCK_NB)
            with patch.object(cleanup.sys, "platform", "darwin"), \
                 patch.dict(cleanup.os.environ, {"CODEX_THREAD_ID": "", "CODEX_SESSION_ID": ""}), \
                 patch.object(cleanup, "macos_active_paths", return_value=set()), \
                 patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")), \
                 patch.object(Path, "rglob", side_effect=AssertionError("unrelated session traversal")):
                active = cleanup.active_paths(codex, (artifact,))
                inactive_activity = cleanup.active_paths(codex, (inactive,))
        self.assertIn(artifact, active)
        self.assertNotIn(unrelated, active)
        self.assertNotIn(inactive, inactive_activity)
        self.assertEqual("would_remove", cleanup.clean_candidate(inactive, self.cutoff, inactive_activity)["action"])
        self.assertEqual("protected", cleanup.clean_candidate(artifact, self.cutoff, active)["reason"])

    def test_activity_outside_codex_skips_session_traversal(self):
        codex = self.root / "codex"
        artifact = self.old_file(codex / "sessions" / "rollout-active-thread.jsonl")
        with patch.object(cleanup.sys, "platform", "darwin"), \
             patch.dict(cleanup.os.environ, {"CODEX_THREAD_ID": "active-thread"}), \
             patch.object(cleanup, "macos_active_paths", return_value=set()), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")), \
             patch.object(Path, "rglob", side_effect=AssertionError("unrelated session traversal")):
            active = cleanup.active_paths(codex, (self.root / "flight",))
        self.assertNotIn(artifact, active)

    def test_codex_deletion_refreshes_scoped_activity_before_removal(self):
        codex = self.root / "codex"
        artifact = self.old_file(codex / "sessions" / "rollout-old.jsonl")
        options = cleanup.argparse.Namespace(repository=self.root, base="base", codex_home=codex,
            sshx_home=self.root / "sshx", tmp_root=[], min_age_hours=1,
            delete=True, verbose=True)
        observations = []
        def activity(root, scopes=(), *, include_sampler_argv=False):
            observations.append((root, scopes, include_sampler_argv))
            return {artifact} if scopes else set()
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", side_effect=activity), \
             patch.object(cleanup, "registered_worktrees", return_value=[]), \
             patch.object(cleanup, "clean_worktrees", return_value=0), contextlib.redirect_stdout(output):
            self.assertEqual(0, cleanup.run_clean(options))
        self.assertEqual([(codex, (), False), (codex, (artifact,), True)], observations)
        items = [json.loads(line) for line in output.getvalue().splitlines()]
        result = next(item for item in items if item.get("path") == str(artifact))
        self.assertEqual(("kept", "changed"), (result["action"], result["reason"]))
        self.assertTrue(artifact.exists())

    def test_remnant_activity_scope_covers_isolated_name_before_deletion(self):
        main = self.root / "main"
        main.mkdir()
        remnant = self.root / "main-residue"
        remnant.mkdir()
        os.utime(remnant, (self.cutoff - 10, self.cutoff - 10))
        options = cleanup.argparse.Namespace(repository=main, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[], min_age_hours=1,
            delete=True, verbose=False)
        observations = []
        def activity(root, scopes=(), *, include_sampler_argv=False):
            observations.append((scopes, include_sampler_argv))
            return {isolated for isolated in self.root.glob("main-residue-cleanup-*")
                    if any(isolated == scope or scope in isolated.parents for scope in scopes)}
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", side_effect=activity), \
             patch.object(cleanup, "registered_worktrees", return_value=[main]), \
             patch.object(cleanup, "remnant_candidates", return_value=[remnant]), \
             patch.object(cleanup, "clean_worktrees", return_value=0), contextlib.redirect_stdout(output):
            self.assertEqual(0, cleanup.run_clean(options))
        self.assertEqual([((), False), ((self.root,), True), ((self.root,), True)], observations)
        items = [json.loads(line) for line in output.getvalue().splitlines()]
        result = next(item for item in items if item.get("category") == "worktree_remnant")
        self.assertEqual(("kept", "changed"), (result["action"], result["reason"]))
        self.assertTrue(remnant.exists())
        self.assertEqual([], list(self.root.glob("main-residue-cleanup-*")))

    def run_rollout_sweep(self, codex, activity, delete=True, registrations=None):
        options = cleanup.argparse.Namespace(repository=self.root, base="base", codex_home=codex,
            sshx_home=self.root / "sshx", tmp_root=[], min_age_hours=1,
            delete=delete, verbose=True)
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", side_effect=activity), \
             patch.object(cleanup, "registered_worktrees", side_effect=registrations, return_value=[]), \
             patch.object(cleanup, "clean_worktrees", return_value=0), contextlib.redirect_stdout(output):
            self.assertEqual(0, cleanup.run_clean(options))
        return [json.loads(line) for line in output.getvalue().splitlines()]

    def test_old_rollout_directory_uses_one_fresh_activity_observation(self):
        codex = self.root / "codex"
        directory = codex / "sessions" / "2026" / "01" / "01"
        rollouts = [self.old_file(directory / ("rollout-" + str(index) + ".jsonl")) for index in range(100)]
        os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
        observations = []
        def activity(root, scopes=(), **kwargs):
            observations.append((root, scopes, kwargs))
            return set()
        for delete in (False, True):
            observations.clear()
            rows = self.run_rollout_sweep(codex, activity, delete)
            items = [row for row in rows if row["event"] == "host_cleanup_item"]
            self.assertEqual(1, len(items))
            self.assertEqual(str(directory), items[0]["path"])
            self.assertEqual("removed" if delete else "would_remove", items[0]["action"])
            self.assertEqual(100 * len("artifact"), rows[-1]["candidate_apparent_bytes"])
            expected = [(codex, (), {})]
            if delete:
                expected.append((codex, (directory,), {"include_sampler_argv": True}))
            self.assertEqual(expected, observations)
            self.assertEqual(not delete, directory.exists())
        self.assertTrue((codex / "sessions").is_dir())
        self.assertTrue(all(not path.exists() for path in rollouts))

    def test_rollout_group_falls_back_for_recent_active_and_unknown_siblings(self):
        for condition in ("recent", "active", "unknown", "subdirectory", "symlink"):
            with self.subTest(condition=condition):
                codex = self.root / condition / "codex"
                directory = codex / "sessions" / "day"
                old = [self.old_file(directory / ("rollout-old-" + str(index) + ".jsonl")) for index in range(2)]
                if condition == "unknown":
                    retained = self.old_file(directory / "private.txt")
                elif condition == "subdirectory":
                    retained = self.old_file(directory / "private" / "notes.txt")
                elif condition == "symlink":
                    retained = directory / "rollout-link.jsonl"
                    retained.symlink_to(self.old_file(self.root / "outside"))
                else:
                    retained = self.old_file(directory / "rollout-retained.jsonl")
                    if condition == "recent":
                        os.utime(retained, None)
                os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
                def activity(*args, **kwargs):
                    return {retained} if condition == "active" else set()
                rows = self.run_rollout_sweep(codex, activity)
                self.assertTrue(retained.exists())
                self.assertTrue(directory.is_dir())
                self.assertTrue(all(not path.exists() for path in old))
                self.assertEqual(2, rows[-1]["counts"]["codex:removed"])

    def test_rollout_group_new_activity_falls_back_without_stranding_old_siblings(self):
        codex = self.root / "codex"
        directory = codex / "sessions" / "day"
        active = self.old_file(directory / "rollout-active.jsonl")
        old = self.old_file(directory / "rollout-old.jsonl")
        os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
        def activity(root, scopes=(), **kwargs):
            return {active} if scopes else set()
        rows = self.run_rollout_sweep(codex, activity)
        self.assertTrue(active.exists())
        self.assertFalse(old.exists())
        self.assertEqual(1, rows[-1]["counts"]["codex:removed"])
        self.assertEqual(1, rows[-1]["counts"]["codex:kept"])

    def test_rollout_group_and_fallback_preserve_newly_registered_ancestor(self):
        codex = self.root / "codex"
        directory = codex / "sessions" / "day"
        rollouts = [self.old_file(directory / ("rollout-" + str(index) + ".jsonl")) for index in range(2)]
        os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
        registered = False
        def activity(root, scopes=(), **kwargs):
            nonlocal registered
            if scopes == (directory,):
                registered = True
            return set()
        def registrations(repository):
            return [codex] if registered else []
        rows = self.run_rollout_sweep(codex, activity, registrations=registrations)
        self.assertTrue(all(path.exists() for path in rollouts))
        self.assertEqual({"codex:kept": 2}, rows[-1]["counts"])

    def test_rollout_group_shape_rechecks_preserve_new_unknown_files(self):
        for phase in ("before_inspection", "refresh"):
            with self.subTest(phase=phase):
                codex = self.root / phase / "codex"
                directory = codex / "sessions" / "day"
                old = [self.old_file(directory / ("rollout-" + str(index) + ".jsonl")) for index in range(2)]
                os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
                unknown = directory / "private.txt"
                group_files = cleanup.rollout_group_files
                def add_unknown():
                    self.old_file(unknown)
                    os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
                def snapshot(path, root):
                    files = group_files(path, root)
                    if files is not None and phase == "before_inspection":
                        add_unknown()
                    return files
                def activity(root, scopes=(), **kwargs):
                    if phase == "refresh" and scopes == (directory,):
                        add_unknown()
                    return set()
                with patch.object(cleanup, "rollout_group_files", side_effect=snapshot):
                    rows = self.run_rollout_sweep(codex, activity)
                self.assertEqual("artifact", unknown.read_text())
                self.assertTrue(directory.is_dir())
                self.assertTrue(all(not path.exists() for path in old))
                self.assertEqual(2, rows[-1]["counts"]["codex:removed"])

    def test_rollout_group_removal_preserves_entries_added_after_final_inspection(self):
        codex = self.root / "codex"
        directory = codex / "sessions" / "day"
        rollouts = [self.old_file(directory / ("rollout-" + str(index) + ".jsonl")) for index in range(2)]
        os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
        unknown = directory / "private.txt"
        nested = directory / "private" / "notes.txt"
        remove = cleanup.remove_rollout_group
        def late_entry(path, filenames, identity):
            unknown.write_text("retain late bytes")
            nested.parent.mkdir()
            nested.write_text("retain nested bytes")
            nested.parent.chmod(0o500)
            self.addCleanup(nested.parent.chmod, 0o700)
            return remove(path, filenames, identity)
        warning = io.StringIO()
        with patch.object(cleanup, "remove_rollout_group", side_effect=late_entry), \
             contextlib.redirect_stderr(warning):
            rows = self.run_rollout_sweep(codex, lambda *args, **kwargs: set())
        self.assertTrue(all(not path.exists() for path in rollouts))
        self.assertEqual("retain late bytes", unknown.read_text())
        self.assertEqual("retain nested bytes", nested.read_text())
        self.assertEqual(0o500, stat.S_IMODE(nested.parent.stat().st_mode))
        result = next(row for row in rows if row.get("path") == str(directory))
        self.assertEqual("failed", result["action"])
        self.assertEqual(1, rows[-1]["counts"]["codex:failed"])
        self.assertEqual(0, rows[-1]["candidate_apparent_bytes"])
        diagnostic = json.loads(warning.getvalue())
        self.assertEqual((str(directory), "failed"), (diagnostic["path"], diagnostic["action"]))

    def test_rollout_groups_preserve_session_and_archive_roots(self):
        codex = self.root / "codex"
        roots = [codex / "sessions", codex / "archived_sessions"]
        for root in roots:
            for index in range(2):
                self.old_file(root / ("rollout-" + str(index) + ".jsonl"))
            os.utime(root, (self.cutoff - 10, self.cutoff - 10))
        self.run_rollout_sweep(codex, lambda *args, **kwargs: set())
        self.assertTrue(all(root.is_dir() and not list(root.iterdir()) for root in roots))

    def test_activity_command_reuses_sampler_and_fails_closed(self):
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", return_value={self.root}), contextlib.redirect_stdout(output):
            self.assertEqual(0, cleanup.main(["active-paths"]))
        self.assertEqual([str(self.root)], json.loads(output.getvalue()))
        with patch.object(cleanup, "active_paths", side_effect=OSError("activity unavailable")), \
             contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(1, cleanup.main(["active-paths"]))

    def test_pidfd_current_identity_is_revalidated_and_descriptors_close(self):
        # Real directory/stat descriptors, with a synthetic /proc endpoint and
        # ready/nonready pidfd poll. Keeping the inode unchanged isolates pid
        # and starttime reuse from the simpler directory-replacement case.
        process = Path("/proc/123")
        endpoint = self.root / "proc-endpoint"
        endpoint.mkdir()
        def write_identity(pid=123, starttime=900):
            (endpoint / "stat").write_text(str(pid) + " (fixture) " +
                " ".join(["S"] + ["0"] * 18 + [str(starttime)]) + "\n")
        real_open, real_close, real_stat = os.open, os.close, os.stat
        for change in ("pid", "starttime", "unavailable", "malformed", "open-failed", "matched"):
            for ready in (False, True):
                with self.subTest(change=change, ready=ready):
                    write_identity()
                    opened, closed, live = [], [], set()
                    def open_fd(name, flags, *args, **kwargs):
                        fd = real_open(endpoint if name == process else name, flags, *args, **kwargs)
                        if name == process or str(name) == os.devnull:
                            opened.append(fd)
                            self.assertNotIn(fd, live)
                            live.add(fd)
                        return fd
                    def close_fd(fd):
                        self.assertIn(fd, live)
                        live.remove(fd)
                        closed.append(fd)
                        real_close(fd)
                    poller = types.SimpleNamespace(register=lambda *a: None,
                        poll=lambda timeout: [(observer.pidfd, select.POLLIN)] if ready else [])
                    with patch.object(cleanup.os, "uname", return_value=types.SimpleNamespace(sysname="Linux")), \
                         patch.object(cleanup.os, "open", side_effect=open_fd), \
                         patch.object(cleanup.os, "close", side_effect=close_fd), \
                         patch.object(cleanup.os, "stat", side_effect=lambda name, *a, **kw:
                                      real_stat(endpoint if name == process else name, *a, **kw)), \
                         patch.object(cleanup.os, "pidfd_open", create=True,
                                      side_effect=lambda pid, flags: open_fd(os.devnull, os.O_RDONLY)), \
                         patch.object(cleanup.LinuxProcessObserver, "pidfd_pid", return_value=123), \
                         patch.object(cleanup.select, "poll", return_value=poller):
                        observer = cleanup.LinuxProcessObserver(process)
                        try:
                            self.assertEqual("matched", observer.binding["identity"], observer.binding)
                            anchor = observer.binding["anchor"]
                            if change == "pid":
                                write_identity(pid=124)
                            elif change == "starttime":
                                write_identity(starttime=901)
                            elif change == "unavailable":
                                (endpoint / "stat").unlink()
                            elif change == "malformed":
                                (endpoint / "stat").write_text("unreadable proc identity")
                            elif change == "open-failed":
                                (endpoint / "stat").unlink()
                                endpoint.rmdir()
                            if change in ("pid", "starttime"):
                                info = endpoint.stat()
                                self.assertEqual((anchor["device"], anchor["inode"]), (info.st_dev, info.st_ino))
                            for _ in range(2):
                                sample = observer.sample(check_current=True)
                                self.assertIn("wall_time_ns", sample)
                                self.assertIn("monotonic_ns", sample)
                                self.assertIn("poll_finished_monotonic_ns", sample)
                                self.assertEqual("matched" if change == "matched" else "unknown", sample["identity"], sample)
                                self.assertEqual(("observed" if ready else "not_observed") if change == "matched"
                                                 else "unknown", sample["group_exit"], sample)
                                self.assertEqual({observer.proc_fd, observer.pidfd}, live)
                        finally:
                            observer.close()
                            observer.close()  # Closing twice must not close a recycled descriptor.
                    self.assertFalse(live)
                    self.assertCountEqual(opened, closed)
                    if not endpoint.exists():
                        endpoint.mkdir()

    @unittest.skipUnless(sys.platform.startswith("linux"), "requires native Linux proc/pidfd")
    def test_native_pidfd_dead_leader_live_worker(self):
        # Observe the leader's actual Z state: Linux pidfd_poll() can defer even
        # PIDFD_THREAD readiness for a group leader with surviving subthreads
        # (fs/pidfs.c, delay_group_leader()). It cannot synchronize this phase.
        # The flags=0 process pidfd must remain nonready while the worker owns
        # cwd/fd until pipe release. Every probe wait is bounded.
        source = r"""
#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <unistd.h>
static const char *directory;
static int release_fd;
static void *worker(void *unused) {
    (void)unused;
    if (chdir(directory)) _exit(10);
    int fd = open("held", O_CREAT | O_RDWR, 0600);
    if (fd < 0) _exit(11);
    long tid = syscall(SYS_gettid);
    if (dprintf(1, "ready %ld %d\n", tid, fd) < 0) _exit(12);
    char command;
    ssize_t count = read(release_fd, &command, 1);
    if (count < 0 || (count == 1 && command != 'X')) _exit(15);
    if (close(fd)) _exit(16);
    return NULL;
}
int main(int argc, char **argv) {
    if (argc != 3) return 17;
    directory = argv[1];
    release_fd = atoi(argv[2]);
    pthread_t thread;
    if (pthread_create(&thread, NULL, worker, NULL)) return 19;
    char command;
    ssize_t count = read(0, &command, 1);
    if (count < 0 || (count == 1 && command != 'L')) return 20;
    // SYS_exit ends this task only; the worker owns the remaining resources.
    syscall(SYS_exit, 0);
    return 21;
}
"""
        probe = self.root / "thread-group-probe"
        compiled = subprocess.run(["cc", "-std=c11", "-pthread", "-Wall", "-Wextra", "-Werror",
                                   "-x", "c", "-o", str(probe), "-"],
                                  input=source, capture_output=True, text=True, timeout=10)
        self.assertEqual(0, compiled.returncode, compiled.stdout + compiled.stderr)
        release_read, release_write = os.pipe()
        try:
            with os.fdopen(release_write, "wb", buffering=0) as release:
                child = subprocess.Popen([str(probe), str(self.root), str(release_read)],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, text=True, pass_fds=(release_read,))
                observer = None
                try:
                    readable, _, _ = select.select([child.stdout], [], [], 10)
                    self.assertTrue(readable, "native probe did not announce its worker; kernel=" + str(os.uname()))
                    ready = os.read(child.stdout.fileno(), 256).decode().split()
                    self.assertEqual(3, len(ready), ready)
                    self.assertEqual("ready", ready[0], ready)
                    worker, held_fd = map(int, ready[1:])
                    process = Path("/proc") / str(child.pid)
                    observer = cleanup.LinuxProcessObserver(process)
                    self.assertEqual("matched", observer.binding["identity"], observer.binding)
                    self.assertEqual(0, observer.sample()["revents"])
                    iterdir = Path.iterdir
                    def only_probe(path):
                        return iter([process]) if path == Path("/proc") else iterdir(path)
                    with patch.object(Path, "iterdir", only_probe):
                        active = cleanup.active_paths(self.root / "codex", scopes=(self.root,))
                    self.assertIn(self.root, active)
                    self.assertIn(self.root / "held", active)
                    child.stdin.write("L")
                    child.stdin.flush()
                    deadline = time.monotonic() + 10
                    while True:
                        status = cleanup.LinuxProcessObserver.read(observer.proc_fd, "status")
                        fields = dict(line.split(":", 1) for line in status.splitlines() if ":" in line)
                        if fields["State"].split()[0] == "Z":
                            break
                        if time.monotonic() >= deadline:
                            self.fail("native leader did not reach Z; kernel=" + str(os.uname()) + "; " + status)
                        time.sleep(0.001)
                    self.assertEqual("Z", fields["State"].split()[0], status)
                    self.assertEqual("2", fields["Threads"].strip(), status)
                    live = observer.sample()
                    self.assertEqual(0, live["revents"], live)
                    self.assertEqual("not_observed", live["group_exit"])
                    # A live worker really holds these paths even when the leader's
                    # inventory is inaccessible. Partial task evidence cannot admit.
                    task = process / "task" / str(worker)
                    self.assertEqual(str(self.root), os.readlink(task / "cwd"))
                    self.assertEqual(str(self.root / "held"), os.readlink(task / "fd" / str(held_fd)))
                    diagnostic = None
                    output, errors = io.StringIO(), io.StringIO()
                    with patch.object(Path, "iterdir", only_probe), \
                         contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
                        original_return_code = cleanup.main(["active-paths", "--scope", str(self.root)])
                    if original_return_code == 1:
                        self.assertEqual("", output.getvalue())
                        prefix = "HOST_CLEANUP_FAILED linux_activity_unavailable "
                        self.assertTrue(errors.getvalue().startswith(prefix), errors.getvalue())
                        refusal = json.loads(errors.getvalue()[len(prefix):])
                        diagnostic = refusal["diagnostic"]
                        self.assertIn(diagnostic["original_error"]["errno"],
                                      (cleanup.errno.EACCES, cleanup.errno.ENOENT, cleanup.errno.ESRCH))
                        self.assertEqual("partial_non_atomic", diagnostic["task_inventory"])
                        for moment in ("fault", "refusal"):
                            self.assertEqual(0, diagnostic[moment]["revents"], diagnostic)
                            self.assertEqual("not_observed", diagnostic[moment]["group_exit"])
                        self.assertLessEqual(diagnostic["fault"]["monotonic_ns"],
                                             diagnostic["refusal"]["monotonic_ns"])
                    else:
                        self.assertEqual(0, original_return_code, errors.getvalue())
                        self.assertIn(str(self.root), json.loads(output.getvalue()))
                        self.assertIn(str(self.root / "held"), json.loads(output.getvalue()))
                    release.write(b"X")
                    release.close()
                    child.stdin.close()
                    self.assertEqual(0, child.wait(timeout=10), child.stderr.read())
                    exited = observer.sample()
                    self.assertTrue(exited["revents"] & select.POLLIN, exited)
                    self.assertEqual("observed", exited["group_exit"])
                    print(json.dumps(dict(probe="native_pidfd_dead_leader_live_worker", live=live,
                                          exited=exited, diagnostic=diagnostic,
                                          kernel=list(os.uname()), leader_state=fields["State"].strip(),
                                          leader_threads=fields["Threads"].strip(),
                                          original_return_code=original_return_code), sort_keys=True), flush=True)
                finally:
                    release.close()
                    if not child.stdin.closed:
                        child.stdin.close()  # EOF releases the leader even on assertion failure.
                    try:
                        child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        child.kill()  # Only this fixture's child, after cooperative EOF failed.
                        child.wait(timeout=5)
                        self.fail("native probe did not exit after EOF cleanup; kernel=" + str(os.uname()))
                    finally:
                        if observer is not None:
                            observer.close()
                        child.stdout.close()
                        child.stderr.close()
        finally:
            os.close(release_read)

    def test_linux_disappearing_links_preserve_observable_siblings(self):
        process = self.root / "proc/123"
        descriptors = process / "fd"
        descriptors.mkdir(parents=True)
        (process / "cwd").symlink_to(self.root)
        target = self.old_file(self.root / "checkout/reader.txt")
        links = [descriptors / str(index) for index in range(3)]
        for link in links:
            link.symlink_to(target if link == links[-1] else self.root)
        iterdir, readlink = Path.iterdir, os.readlink
        def inventory(path):
            if path == Path("/proc"):
                return iter([process])
            if path == descriptors:
                return iter(links)
            return iterdir(path)
        for position in (0, 1):
            for error in (FileNotFoundError, ProcessLookupError):
                with self.subTest(position=position, error=error.__name__):
                    observed = []
                    def interrupted(link):
                        observed.append(link)
                        if link == links[position]:
                            raise error("handle disappeared")
                        return readlink(link)
                    with patch.object(cleanup.sys, "platform", "linux"), \
                         patch.object(Path, "iterdir", inventory), \
                         patch.object(cleanup.os, "readlink", interrupted), \
                         patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
                        self.assertIn(target.resolve(), cleanup.active_paths(self.root / "codex"))
                    self.assertIn(links[-1], observed)

    def test_linux_unverifiable_live_process_observation_fails_closed(self):
        process = self.root / "proc/123"
        descriptors = process / "fd"
        descriptors.mkdir(parents=True)
        iterdir = Path.iterdir
        for boundary in ("cwd", "fd"):
            with self.subTest(boundary=boundary):
                def inventory(path):
                    if path == Path("/proc"):
                        return iter([process])
                    if path == descriptors and boundary == "fd":
                        raise FileNotFoundError("descriptor inventory disappeared")
                    return iterdir(path)
                with patch.object(cleanup.sys, "platform", "linux"), \
                     patch.object(Path, "iterdir", inventory), \
                     contextlib.redirect_stdout(io.StringIO()) as output, \
                     contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(1, cleanup.main(["active-paths"]))
                self.assertEqual("", output.getvalue())

    def test_linux_terminal_group_requires_complete_single_thread_evidence(self):
        process = self.root / "proc/123"
        (process / "fd").mkdir(parents=True)
        task = process / "task/123"
        task.mkdir(parents=True)
        target = self.old_file(self.root / "checkout/reader.txt")
        (process / "fd/1").symlink_to(target)
        (process / "cwd").symlink_to(self.root)
        iterdir, readlink = Path.iterdir, os.readlink
        def inventory(path):
            return iter([process]) if path == Path("/proc") else iterdir(path)
        def denied(path):
            if path == process / "cwd":
                raise PermissionError("cwd is unavailable")
            return readlink(path)
        with patch.object(cleanup.sys, "platform", "linux"), \
             patch.object(Path, "iterdir", inventory), \
             patch.object(cleanup.os, "readlink", denied), \
             patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
            for state, threads, complete, terminal in (
                    ("Z", "1", True, True), ("X", "1", True, True),
                    ("S", "1", True, False), ("Z", "2", True, False),
                    ("Z", "1", False, False)):
                with self.subTest(state=state, threads=threads, complete=complete):
                    (process / "status").write_text("State: " + state + "\nThreads: " + threads + "\n")
                    if complete:
                        (task / "status").write_text("State: " + state + "\nThreads: " + threads + "\n")
                    else:
                        (task / "status").unlink()
                    if terminal:
                        cleanup.active_paths(self.root / "codex")
                    else:
                        with self.assertRaisesRegex(OSError, "linux_activity_unavailable"):
                            cleanup.active_paths(self.root / "codex")
            # A terminal leader cannot hide a live sibling's cwd or descriptors.
            sibling = process / "task/124"
            sibling.mkdir()
            (sibling / "status").write_text("State: S\nThreads: 2\n")
            (process / "status").write_text("State: Z\nThreads: 2\n")
            (task / "status").write_text("State: Z\nThreads: 2\n")
            with self.assertRaisesRegex(OSError, "linux_activity_unavailable"):
                cleanup.active_paths(self.root / "codex")

    def test_linux_exited_process_does_not_hide_other_process_activity(self):
        exited = self.root / "proc/122"
        live = self.root / "proc/123"
        (exited / "fd").mkdir(parents=True)
        (exited / "cwd").symlink_to(self.root)
        (live / "fd").mkdir(parents=True)
        (live / "cwd").symlink_to(self.root)
        target = self.old_file(self.root / "checkout/reader.txt")
        (live / "fd/1").symlink_to(target)
        iterdir, path_stat, readlink = Path.iterdir, Path.stat, os.readlink
        for boundary in ("stat", "fd", "cwd"):
            with self.subTest(boundary=boundary):
                gone = boundary == "stat"
                def process_stat(path, *args, **kwargs):
                    if path == exited and gone:
                        raise FileNotFoundError("process exited")
                    return path_stat(path, *args, **kwargs)
                def inventory(path):
                    nonlocal gone
                    if path == Path("/proc"):
                        return iter([exited, live])
                    if path == exited / "fd" and boundary == "fd":
                        gone = True
                        raise ProcessLookupError("process exited during descriptor inventory")
                    return iterdir(path)
                def link(path):
                    nonlocal gone
                    if path == exited / "cwd" and boundary == "cwd":
                        gone = True
                        raise FileNotFoundError("process exited during cwd observation")
                    return readlink(path)
                with patch.object(cleanup.sys, "platform", "linux"), \
                     patch.object(Path, "iterdir", inventory), \
                     patch.object(Path, "stat", process_stat), \
                     patch.object(cleanup.os, "readlink", link), \
                     patch.object(cleanup.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
                    self.assertIn(target.resolve(), cleanup.active_paths(self.root / "codex"))

    def test_linux_activity_transition_waits_for_matched_group_exit_only(self):
        process = self.root / "proc/43117"
        process.mkdir(parents=True)
        anchor = dict(device=27, inode=235306, pid=43117, starttime=56497)
        sample = dict(identity="matched", group_exit="not_observed", revents=0, current=anchor)
        inventory_started = dict(identity="matched", group_exit="not_observed", revents=0)
        diagnostic = dict(
            task_inventory="partial_non_atomic",
            binding=dict(identity="matched", anchor=anchor, current=anchor, pidfd_pid=43117),
            fault=sample,
            refusal=sample,
            inventory_started=inventory_started,
        )
        error = OSError("linux_activity_unavailable " + json.dumps(dict(
            process=str(process), boundary="fd_inventory", diagnostic=diagnostic)))
        waits = []

        class Observer:
            def __init__(self, observed):
                self.binding = dict(identity="matched", anchor=anchor, current=anchor, pidfd_pid=43117)

            def wait_for_group_exit(self, timeout_ms):
                waits.append(timeout_ms)
                return True

            def close(self):
                pass

        with patch.object(cleanup, "LinuxProcessObserver", Observer):
            self.assertTrue(cleanup.wait_for_linux_activity_transition(error))
        self.assertEqual([1000], waits)

    def test_linux_activity_transition_keeps_persistent_inaccessible_process_refused(self):
        process = self.root / "proc/43117"
        process.mkdir(parents=True)
        anchor = dict(device=27, inode=235306, pid=43117, starttime=56497)
        sample = dict(identity="matched", group_exit="not_observed", revents=0, current=anchor)
        inventory_started = dict(identity="matched", group_exit="not_observed", revents=0)
        diagnostic = dict(
            task_inventory="partial_non_atomic",
            binding=dict(identity="matched", anchor=anchor, current=anchor, pidfd_pid=43117),
            fault=sample,
            refusal=sample,
            inventory_started=inventory_started,
        )
        error = OSError("linux_activity_unavailable " + json.dumps(dict(
            process=str(process), boundary="fd_inventory", diagnostic=diagnostic)))

        class Observer:
            def __init__(self, observed):
                self.binding = dict(identity="matched", anchor=anchor, current=anchor, pidfd_pid=43117)

            def wait_for_group_exit(self, timeout_ms):
                return False

            def close(self):
                pass

        with patch.object(cleanup, "LinuxProcessObserver", Observer):
            self.assertFalse(cleanup.wait_for_linux_activity_transition(error))

    def test_inventory_failure_reports_already_removed_artifacts(self):
        artifact = self.old_file(self.root / "tmp" / "old-output")
        options = cleanup.argparse.Namespace(
            repository=self.root, base="base", codex_home=self.root / "codex",
            sshx_home=self.root / "sshx", tmp_root=[self.root / "tmp"],
            min_age_hours=1, delete=True, verbose=False)
        def interrupted_inventory(*args, **kwargs):
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

    def test_protected_flag_anywhere_keeps_entire_candidate(self):
        artifact = self.old_file(self.root / "service" / "nested" / "state")
        for directory in (artifact.parent, artifact.parent.parent):
            os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
        lstat = Path.lstat
        for flag in (stat.UF_IMMUTABLE, stat.UF_APPEND, stat.UF_NOUNLINK,
                     stat.SF_IMMUTABLE, stat.SF_APPEND, stat.SF_NOUNLINK):
            def flagged(path):
                info = lstat(path)
                if path != artifact.parent:
                    return info
                fields = {name: getattr(info, name) for name in dir(info) if name.startswith("st_")}
                return types.SimpleNamespace(**dict(fields, st_flags=flag))
            with self.subTest(flag=hex(flag)), patch.object(Path, "lstat", flagged), \
                 patch.object(cleanup.shutil, "rmtree") as rmtree:
                result = cleanup.clean_candidate(artifact.parent.parent, self.cutoff, [], delete=True)
                self.assertEqual(("kept", "protected_flag"), (result["action"], result["reason"]),
                                 "[FAIL] protected_flag_candidate_kept")
                rmtree.assert_not_called()
        self.assertTrue(artifact.exists())

    @unittest.skipUnless(sys.platform == "darwin" and hasattr(os, "chflags"), "BSD file flags")
    def test_real_immutable_flag_is_retained_without_failure(self):
        artifact = self.old_file(self.root / "service" / "state")
        os.utime(artifact.parent, (self.cutoff - 10, self.cutoff - 10))
        os.chflags(artifact, stat.UF_IMMUTABLE)
        self.addCleanup(os.chflags, artifact, 0)
        result = cleanup.clean_candidate(artifact.parent, self.cutoff, [], delete=True)
        self.assertEqual(("kept", "protected_flag"), (result["action"], result["reason"]),
                         "[FAIL] real_immutable_candidate_kept")
        self.assertTrue(artifact.exists())

    def test_owned_read_only_tree_is_removed_without_following_links(self):
        outside = self.root / "outside"
        outside.mkdir()
        packet = self.root / "packet"
        sealed = packet / "sealed"
        self.old_file(sealed / "ENTRY.md")
        link = sealed / "external"
        link.symlink_to(outside, target_is_directory=True)
        os.utime(link, (self.cutoff - 10, self.cutoff - 10), follow_symlinks=False)
        for directory in (sealed, packet, outside):
            os.utime(directory, (self.cutoff - 10, self.cutoff - 10))
            directory.chmod(0o555)
            self.addCleanup(lambda directory=directory: directory.exists() and directory.chmod(0o755))
        result = cleanup.clean_candidate(packet, self.cutoff, [], delete=True)
        self.assertEqual("removed", result["action"], "[FAIL] read_only_owned_tree_removed")
        self.assertFalse(packet.exists(), "[FAIL] read_only_owned_tree_absent")
        self.assertEqual(0o555, stat.S_IMODE(outside.lstat().st_mode), "[FAIL] read_only_removal_stays_inside_tree")


if __name__ == "__main__":
    unittest.main()
