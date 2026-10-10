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

    def test_clean_lanes_receives_large_activity_through_one_file(self):
        active = {self.root / ("active-" + str(index) + "-" + "x" * 160) for index in range(20000)}
        observed = {}

        def run(arguments, **_):
            position = arguments.index("--active-paths-file")
            source = Path(arguments[position + 1])
            observed.update(arguments=arguments, source=source, paths=json.loads(source.read_text()),
                            mode=source.stat().st_mode & 0o777)
            return subprocess.CompletedProcess(arguments, 0)

        with patch.object(cleanup.subprocess, "run", side_effect=run):
            self.assertEqual(0, cleanup.clean_worktrees(self.root, "base", True, active))
        self.assertNotIn("--active-path", observed["arguments"], "[FAIL] clean_lanes_activity_not_in_argv")
        self.assertLess(sum(len(os.fsencode(argument)) + 1 for argument in observed["arguments"]), 4096,
                        "[FAIL] clean_lanes_argv_bounded")
        self.assertEqual(sorted(str(path.resolve()) for path in active), observed["paths"],
                         "[FAIL] clean_lanes_activity_file_content")
        self.assertEqual(0o600, observed["mode"], "[FAIL] clean_lanes_activity_file_private")
        self.assertFalse(observed["source"].exists(), "[FAIL] clean_lanes_activity_file_removed")

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

    def test_aggregate_temporary_sweep_qualifies_bytes_and_retains_unknown(self):
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
        options = cleanup.argparse.Namespace(repository=repository, base="dev",
            codex_home=self.root / "codex", sshx_home=self.root / "sshx", tmp_root=[temporary],
            min_age_hours=0, delete=True, verbose=False)
        with patch.object(cleanup, "clean_worktrees", return_value=0), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(0, cleanup.run_clean(options))
        self.assertFalse(safe.exists())
        self.assertEqual("recovery\n", (unknown / "private").read_text())

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

    def test_activity_command_reuses_sampler_and_fails_closed(self):
        output = io.StringIO()
        with patch.object(cleanup, "active_paths", return_value={self.root}), contextlib.redirect_stdout(output):
            self.assertEqual(0, cleanup.main(["active-paths"]))
        self.assertEqual([str(self.root)], json.loads(output.getvalue()))
        with patch.object(cleanup, "active_paths", side_effect=OSError("activity unavailable")), \
             contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(1, cleanup.main(["active-paths"]))

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
