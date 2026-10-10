"""Real Git/OS correspondence probes; no production test modes or timing gates."""

import argparse
from contextlib import ExitStack
import importlib.util
import json
import os
from pathlib import Path
import select
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from native_fixture import NativeFixture
from mirror_fixture import MirrorCases

ROOT = Path(sys.argv.pop(1)).resolve()
SCRIPT = ROOT / "tools/scripts/worktree/worktree_protocol.py"
sys.path.insert(0, str(SCRIPT.parent))
import worktree_protocol as protocol
import worktree_preservation as preservation


class ProtocolTests(MirrorCases, NativeFixture):
    def setUp(self):
        self.root = self.workspace("worktree-contract-")
        self.note("setup.begin")
        self.main = self.root / "main"
        self.main.mkdir()
        self.remote = self.root / "remote.git"
        self.g(self.root, "init", "--bare", self.remote)
        self.g(self.main, "init", "--initial-branch=dev")
        self.g(self.main, "config", "user.name", "Protocol Tests")
        self.g(self.main, "config", "user.email", "protocol@example.invalid")
        for name in ("owned", "other", "dir/child"):
            file = self.main / name
            file.parent.mkdir(exist_ok=True)
            file.write_text("original\n")
        (self.main / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (self.main / "lake-manifest.json").write_text('{"packages":[]}\n')
        self.g(self.main, "add", ".")
        self.g(self.main, "commit", "-m", "baseline")
        self.base = self.g(self.main, "rev-parse", "HEAD").strip()
        self.g(self.main, "remote", "add", "origin", self.remote)
        self.g(self.main, "push", "origin", "dev")
        self.tree = self.root / "tree"
        self.branch = "lane/governance/fixture"
        self.g(self.main, "worktree", "add", "-b", self.branch, self.tree, "HEAD")
        self.jobs = []
        self.addCleanup(self.stop_jobs)
        self.note("setup.end")

    def note(self, phase, **values):
        print(json.dumps(dict(probe=self._testMethodName, root=str(self.root),
            phase=phase, fixture_pid=os.getpid(), monotonic=time.monotonic(), **values)),
            file=sys.stderr, flush=True)

    def stop_jobs(self):
        self.jobs_settled = False
        for job in self.jobs:
            self.note("job.settle.begin", native_pid=job.pid, returncode=job.poll())
            if job.poll() is None:
                job.kill()
            job.communicate(timeout=10)
            self.note("job.settle.end", native_pid=job.pid, returncode=job.returncode)
        self.jobs_settled = True

    def g(self, root, *args):
        command = ["git", "-C", str(root), *map(str, args)]
        result = self.run_owned_command(command, self.root, phase="git", timeout=300,
                                        check=False, env=protocol.git_environment(), pass_fds=protocol.scope_fds())
        if result.returncode:
            raise protocol.Refused(result.stderr.strip() or "git failed")
        return result.stdout

    def run_protocol(self, *args, expect=0, env=None):
        command = [sys.executable, "-B", str(SCRIPT), "--source", str(self.main), *map(str, args)]
        result = self.run_owned_command(command, self.root, phase="protocol", timeout=30, check=False, env=env)
        self.assertEqual(expect, result.returncode, result.stdout + result.stderr)
        return result

    def hold(self, *scopes, code=None):
        code = code or 'import sys; print("ready",flush=True); sys.stdin.readline()'
        job = subprocess.Popen([sys.executable, "-B", str(SCRIPT), "--source", str(self.main),
            "with", "--path", str(self.tree), *scopes, "--", sys.executable, "-c", code],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.jobs.append(job)
        self.jobs_settled = False
        self.note("hold.readiness.begin", command=job.args, native_pid=job.pid, guard_seconds=10)
        self.assertTrue(select.select([job.stdout], [], [], 10)[0], "job readiness timeout")
        self.assertEqual("ready\n", job.stdout.readline(), job.stderr.read() if job.poll() is not None else "")
        self.note("hold.readiness.end", native_pid=job.pid)
        return job

    def remove(self, expect=0, *args):
        return self.run_protocol("remove", "--names", "tree", *args, expect=expect)

    def checkpoint(self, *args, expect=0):
        message = self.root / "message"
        message.write_text("authorized unit\n")
        return self.run_protocol("checkpoint", "--path", self.tree,
                                 "--message-file", message, *args, expect=expect)

    def test_cross_session_dirty_reuse_preserves_bytes(self):
        (self.tree / "owned").write_text("dirty\n")
        self.run_protocol("reuse", "--path", self.tree, "--branch", self.branch, "--base", self.base)
        self.assertEqual("dirty\n", (self.tree / "owned").read_text())

    def test_incompatible_reuse_and_pin_preserve_tree(self):
        self.run_protocol("reuse", "--path", self.tree, "--branch", "other", "--base", self.base, expect=73)
        (self.tree / "lean-toolchain").write_text("changed\n")
        self.run_protocol("reuse", "--path", self.tree, "--branch", self.branch, "--base", self.base, expect=73)
        self.assertEqual("changed\n", (self.tree / "lean-toolchain").read_text())

    def test_shared_participants_and_disjoint_writers(self):
        self.hold("--write", "owned")
        self.hold("--write", "other")
        self.run_protocol("with", "--path", self.tree, "--write", "owned", "--", "true", expect=73)
        self.run_protocol("with", "--path", self.tree, "--exclusive", "--", "true", expect=73)

    def test_semantic_read_blocks_descendant_write(self):
        self.hold("--read", "dir")
        self.run_protocol("with", "--path", self.tree, "--write", "dir/child", "--", "true", expect=73)
        self.run_protocol("with", "--path", self.tree, "--write", "owned", "--", "true")

    def test_normal_and_abrupt_exit_release(self):
        job = self.hold("--write", "owned")
        job.communicate("exit\n", timeout=10)
        self.run_protocol("with", "--path", self.tree, "--write", "owned", "--", "true")
        job = self.hold("--write", "owned")
        job.kill()
        job.communicate(timeout=10)
        self.run_protocol("with", "--path", self.tree, "--write", "owned", "--", "true")

    def test_surviving_descendant_retains_scope(self):
        pidfile = self.root / "child.pid"
        code = ('import os,sys,time; child=os.fork(); '
                f'open({str(pidfile)!r},"w").write(str(child)) if child else None; '
                'print("ready",flush=True) if child else None; time.sleep(30)')
        job = self.hold("--write", "owned", code=code)
        child = int(pidfile.read_text())
        try:
            job.kill()
            job.wait(timeout=10)
            self.run_protocol("with", "--path", self.tree, "--exclusive", "--", "true", expect=73)
        finally:
            os.kill(child, signal.SIGKILL)

    def test_ordinary_checkpoint_commits_final_working_snapshot(self):
        self.hold("--write", "other")
        (self.tree / "other").write_text("staged version\n")
        self.g(self.tree, "add", "other")
        (self.tree / "other").write_text("working version\n")
        (self.tree / "owned").write_text("current tracked\n")
        (self.tree / "untracked").write_text("current untracked\n")
        (self.main / ".git/info/exclude").write_text("ignored-output\n")
        (self.tree / "ignored-output").write_text("not a snapshot obligation\n")
        self.checkpoint()
        for name, value in (("other", "working version\n"), ("owned", "current tracked\n"),
                            ("untracked", "current untracked\n")):
            self.assertEqual(value, self.g(self.tree, "show", "HEAD:" + name))
        self.assertEqual("", self.g(self.tree, "status", "--porcelain"))
        self.assertNotEqual(0, protocol.git(self.tree, "cat-file", "-e", "HEAD:ignored-output", check=False).returncode)

    def test_publication_equality_ancestry_and_failure(self):
        (self.tree / "owned").write_text("authorized\n")
        self.checkpoint()
        old = self.g(self.tree, "rev-parse", "HEAD").strip()
        args = ["publish", "--path", self.tree, "--branch", self.branch]
        result = json.loads(self.run_protocol(*args).stdout)
        self.assertEqual("equal", result["relation"])
        (self.tree / "owned").write_text("next\n")
        self.checkpoint()
        self.run_protocol(*args)
        result = json.loads(self.run_protocol(*args, "--commit", old).stdout)
        self.assertEqual("ancestor", result["relation"])
        self.g(self.main, "remote", "set-url", "origin", self.root / "missing.git")
        self.run_protocol(*args, expect=73)
        self.assertTrue(self.tree.exists())
        self.assertEqual("next\n", (self.tree / "owned").read_text())

    def test_commit_hook_failure_retains_tree_and_reports_partial_batch(self):
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "second", second, "HEAD")
        (self.tree / "owned").write_text("recover first\n")
        (second / "owned").write_text("reject this snapshot\n")
        hook = self.main / ".git/hooks/pre-commit"
        hook.write_text('#!/bin/sh\nif test "$(git branch --show-current)" = second; then echo native-hook-rejected >&2; exit 1; fi\n')
        hook.chmod(0o755)
        result = self.run_protocol("remove", "--names", "tree second", expect=74)
        rows = json.loads(result.stdout)["items"]
        self.assertEqual(["removed", "checkpoint_failed"], [row["outcome"] for row in rows])
        self.assertIn("native-hook-rejected", rows[1]["error"])
        self.assertFalse(self.tree.exists())
        self.assertTrue(second.exists())
        self.assertEqual(self.base, self.g(second, "rev-parse", "HEAD").strip())
        self.assertEqual("reject this snapshot\n", (second / "owned").read_text())
        self.assertEqual("recover first\n", self.g(self.main, "show", self.branch + ":owned"))

    def test_checkpoint_retry_after_native_index_lock(self):
        self.recover_checkpoint("checkpoint")

    def test_finalization_retries_ordinary_checkpoint(self):
        self.recover_checkpoint("finalize")

    def recover_checkpoint(self, recovery):
        (self.tree / "owned").write_text("current snapshot\n")
        (self.tree / "other").write_text("included staging\n")
        self.g(self.tree, "add", "other")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        lock.write_text("native operation\n")
        self.checkpoint(expect=73)
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        lock.unlink()
        args = [recovery, "--path", self.tree, "--message-file", self.root / "message"]
        if recovery == "finalize":
            args += ["--branch", self.branch, "--writers-joined"]
        self.run_protocol(*args)
        self.assertEqual("current snapshot\n", self.g(self.tree, "show", "HEAD:owned"))
        self.assertEqual("included staging\n", self.g(self.tree, "show", "HEAD:other"))
        self.assertEqual("", self.g(self.tree, "status", "--porcelain"))

    def test_publication_uses_push_url_and_confirms_that_endpoint(self):
        destination = self.root / "push.git"
        self.g(self.root, "init", "--bare", destination)
        self.g(self.main, "remote", "set-url", "--push", "origin", destination)
        (self.tree / "owned").write_text("authorized\n")
        self.checkpoint()
        commit = self.g(self.tree, "rev-parse", "HEAD").strip()
        result = json.loads(self.run_protocol("publish", "--path", self.tree, "--branch", self.branch).stdout)
        self.assertEqual("confirmed", result["status"])
        self.assertEqual(commit + "\n", self.g(destination, "for-each-ref", "--format=%(objectname)", "refs/heads/" + self.branch))
        self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + self.branch))
        (self.tree / "owned").write_text("later\n")
        self.checkpoint()
        self.run_protocol("publish", "--path", self.tree, "--branch", self.branch)
        result = json.loads(self.run_protocol("publish", "--path", self.tree, "--branch", self.branch,
                                              "--commit", commit).stdout)
        self.assertEqual("ancestor", result["relation"])

    def test_publication_refuses_multiple_push_destinations_before_writing(self):
        destination = self.root / "push.git"
        self.g(self.root, "init", "--bare", destination)
        for endpoint in (self.remote, destination):
            self.g(self.main, "config", "--add", "remote.origin.pushurl", endpoint)
        self.run_protocol("publish", "--path", self.tree, "--branch", self.branch, expect=73)
        mirror = self.root / "unsupported-mirror"
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", "mirror/unsupported",
                          "--base", self.base, "--merge", self.base, "--message", "unsupported", expect=73)
        self.assertFalse(mirror.exists())
        self.assertEqual("", self.g(self.main, "for-each-ref", "refs/heads/mirror/unsupported"))
        for endpoint in (self.remote, destination):
            self.assertEqual("", self.g(endpoint, "for-each-ref", "refs/heads/" + self.branch))

    def test_publication_honors_push_instead_of(self):
        destination = self.root / "rewritten.git"
        self.g(self.root, "init", "--bare", destination)
        self.g(self.main, "config", "url." + str(destination) + ".pushInsteadOf", self.remote)
        self.run_protocol("publish", "--path", self.tree, "--branch", self.branch)
        self.assertEqual(self.base + "\n", self.g(destination, "for-each-ref", "--format=%(objectname)",
                                                  "refs/heads/" + self.branch))
        self.assertEqual("", self.g(self.remote, "for-each-ref", "refs/heads/" + self.branch))

    def test_clean_remote_preserved_removal_and_main_protection(self):
        self.remove()
        self.assertFalse(self.tree.exists())
        self.run_protocol("remove", "--names", "main", expect=73)

    def test_unpublished_nested_content_is_checkpointed(self):
        unknown = self.tree / "deep" / "private"
        unknown.parent.mkdir()
        unknown.write_text("unpublished recovery\n")
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_busy_participant_does_not_veto_removal(self):
        job = self.hold("--exclusive")
        self.remove()
        self.assertFalse(self.tree.exists())
        self.assertIsNone(job.poll())

    def test_recycle_without_remote_recovers_final_snapshot_from_retained_branch(self):
        (self.tree / "owned").write_text("staged version\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("final tracked\n")
        (self.tree / "untracked").write_text("final untracked\n")
        (self.main / ".git/info/exclude").write_text("ignored-output\n")
        (self.tree / "ignored-output").write_text("excluded\n")
        self.g(self.main, "remote", "remove", "origin")
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("committed", result["checkpoint"]["status"])
        self.assertEqual("refs/heads/" + self.branch, result["recovery_branch"])
        self.assertFalse(self.tree.exists())
        recovered = self.root / "recovered"
        self.g(self.main, "worktree", "add", recovered, self.branch)
        self.assertEqual("final tracked\n", (recovered / "owned").read_text())
        self.assertEqual("final untracked\n", (recovered / "untracked").read_text())
        self.assertFalse((recovered / "ignored-output").exists())
        self.note("native-recovery", branch=self.branch, commit=result["checkpoint"]["commit"],
                  files=["owned", "untracked"], remote=False)

    def test_clean_local_only_branch_is_retained_without_empty_commit(self):
        (self.tree / "owned").write_text("local commit\n")
        self.checkpoint()
        local = self.g(self.tree, "rev-parse", "HEAD").strip()
        self.g(self.main, "remote", "remove", "origin")
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("unchanged", result["checkpoint"]["status"])
        self.assertEqual(local, self.g(self.main, "rev-parse", self.branch).strip())
        self.g(self.main, "worktree", "add", self.tree, self.branch)
        self.assertEqual("local commit\n", (self.tree / "owned").read_text())

    def test_unfinished_operation_retains_tree_but_cache_use_does_not_veto(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        marker = metadata / "MERGE_HEAD"
        marker.write_text(self.base + "\n")
        (self.tree / "owned").write_text("outstanding\n")
        result = self.remove(74)
        self.assertIn("unfinished_operation:MERGE_HEAD", result.stdout)
        self.assertTrue(self.tree.exists())
        self.assertEqual("", self.g(self.tree, "diff", "--cached", "--name-only"))
        marker.unlink()
        with ExitStack() as stack:
            stack.enter_context(protocol.lock_file(
                self.root / "cache-guards", str((self.tree / ".lake").resolve()), True))
            self.remove()
        self.assertFalse(self.tree.exists())

    def test_detached_checkout_is_retained_with_specific_failure(self):
        self.g(self.tree, "checkout", "--detach")
        (self.tree / "owned").write_text("uncommitted detached\n")
        result = self.remove(74)
        self.assertIn("checkpoint_current_branch_required", result.stdout)
        self.assertTrue(self.tree.exists())
        self.assertEqual("uncommitted detached\n", (self.tree / "owned").read_text())

    def test_whole_batch_preflight_preserves_eligible_member(self):
        other = self.root / "second"
        self.g(self.main, "worktree", "add", "--detach", other, "HEAD")
        self.g(self.main, "worktree", "lock", "--reason", "manual", other)
        (self.tree / "owned").write_text("not checkpointed\n")
        self.run_protocol("remove", "--names", "tree second", expect=68)
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        self.assertEqual("", self.g(self.tree, "diff", "--cached", "--name-only"))
        self.assertTrue(self.tree.exists())

    def test_manual_and_initialization_locks_use_24_hours(self):
        for reason in ("manual", "worktree-init:" + "a" * 32, "", "worktree-init:malformed"):
            with self.subTest(reason=reason):
                self.g(self.main, "worktree", "lock", "--reason", reason, self.tree)
                metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
                lock = metadata / "locked"
                self.remove(68)
                now = time.time()
                os.utime(lock, (now - 86400 + 60, now - 86400 + 60))
                self.remove(68)
                os.utime(lock, (now - 86400 - 60, now - 86400 - 60))
                self.remove(0, "--preview")
                self.assertTrue(self.tree.exists())
                self.g(self.main, "worktree", "unlock", self.tree)
        self.g(self.main, "worktree", "lock", "--reason", "manual", self.tree)
        os.utime(lock, (now - 86400 - 60, now - 86400 - 60))
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_activity_inspection_is_not_a_removal_dependency(self):
        from unittest.mock import patch
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        native_run = subprocess.run
        def run(arguments, *args, **kwargs):
            self.assertFalse(any("host-cleanup.py" in str(arg) or str(arg) == "lsof" for arg in arguments))
            return native_run(arguments, *args, **kwargs)
        with patch.object(subprocess, "run", side_effect=run):
            self.assertEqual("succeeded", preservation.remove(options)["status"])
        self.assertFalse(self.tree.exists())

    def test_invoking_cwd_tree_can_be_removed_before_remaining_batch(self):
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "second", second, "HEAD")
        result = self.run_owned_command([sys.executable, "-B", str(SCRIPT), "--source", str(self.tree),
            "remove", "--names", "tree second"], self.tree, phase="remove-from-target", timeout=30)
        self.assertEqual(["removed", "removed"], [item["outcome"] for item in json.loads(result.stdout)["items"]])
        self.assertFalse(self.tree.exists())
        self.assertFalse(second.exists())
        self.assertTrue(self.main.exists())

    def test_native_partial_removal_reports_actual_effects_and_continues(self):
        self.g(self.main, "worktree", "lock", "--reason", "manual", self.tree)
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        os.utime(metadata / "locked", (1577836800, 1577836800))
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "-b", "second", second, "HEAD")
        binary = self.root / "failure-shim"
        binary.mkdir()
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!{sys.executable}
import os,subprocess,sys
if "remove" in sys.argv and {str(self.tree)!r} in sys.argv:
    result=subprocess.run([{real_git!r}]+sys.argv[1:],close_fds=False)
    if result.returncode==0:
        print("failure after native side effects",file=sys.stderr)
        raise SystemExit(1)
os.execv({real_git!r},[{real_git!r}]+sys.argv[1:])
''')
        shim.chmod(0o755)
        environment = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"])
        result = self.run_protocol("remove", "--names", "tree second", expect=74, env=environment)
        outcomes = json.loads(result.stdout)["items"]
        self.assertEqual(["partial_or_indeterminate", "removed"], [item["outcome"] for item in outcomes])
        self.assertFalse(self.tree.exists())
        self.assertFalse(second.exists())
        self.assertEqual(self.base, self.g(self.main, "rev-parse", "refs/heads/" + self.branch).strip())

    def test_true_ignored_and_unmerged_material(self):
        exclude = self.main / ".git/info/exclude"
        exclude.write_text("private-output\n")
        (self.tree / "private-output").write_text("private bytes\n")
        self.assertEqual("", self.g(self.tree, "status", "--porcelain"))

        oid = self.g(self.tree, "rev-parse", "HEAD:owned").strip()
        protocol.git(self.tree, "update-index", "--index-info",
                     input=f"100644 {oid} 1\towned\n100644 {oid} 2\towned\n".encode())
        self.assertTrue(self.g(self.tree, "ls-files", "--unmerged"))
        result = self.remove(74)
        self.assertIn("unmerged_index", result.stdout)
        self.assertTrue(self.tree.exists())
        self.assertTrue(self.g(self.tree, "ls-files", "--unmerged"))

    def recovery_resolved_conflict_does_not_veto_removal(self):
        oid = self.g(self.tree, "rev-parse", "HEAD:owned").strip()
        protocol.git(self.tree, "update-index", "--index-info",
                     input=f"0 {'0' * len(oid)}\towned\n100644 {oid} 1\towned\n100644 {oid} 2\towned\n".encode())
        (self.tree / "owned").write_text("resolved\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("original\n")
        self.g(self.tree, "add", "owned")
        self.assertEqual("", self.g(self.tree, "status", "--porcelain"))
        self.assertTrue(self.g(self.tree, "ls-files", "--resolve-undo"))
        self.remove()
        self.assertFalse(self.tree.exists())

    def recovery_published_prior_commit_message_is_reconstructable(self):
        (self.tree / "owned").write_text("native commit\n")
        self.g(self.tree, "add", "owned")
        self.g(self.tree, "commit", "-m", "native unit")
        (self.tree / "owned").write_text("checkpoint unit\n")
        self.checkpoint()
        self.run_protocol("publish", "--path", self.tree, "--branch", self.branch)
        self.remove()
        self.assertFalse(self.tree.exists())

    def recovery_local_repository_is_not_a_remote(self):
        (self.tree / "owned").write_text("local recovery\n")
        self.checkpoint()
        local = self.g(self.tree, "rev-parse", "HEAD").strip()
        self.g(self.main, "remote", "set-url", "origin", self.main)
        result = self.run_protocol("publish", "--path", self.tree, "--branch", self.branch, expect=73)
        self.assertIn("remote_is_local_repository", result.stderr)
        self.assertEqual("local recovery\n", (self.tree / "owned").read_text())
        self.remove()
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", local, expect=73)
        self.assertEqual(local, self.g(self.main, "rev-parse", "refs/heads/" + self.branch).strip())

    def recovery_checkpoint_protects_message_reads(self):
        (self.tree / "owned").write_text("working snapshot\n")
        message = self.tree / "checkpoint-message"
        message.write_text("unit message\n")
        writer = self.hold("--write", message.name)
        self.checkpoint("--message-file", message, expect=73)
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        writer.communicate("joined\n", timeout=10)
        self.checkpoint("--message-file", message)
        self.assertEqual("working snapshot\n", self.g(self.tree, "show", "HEAD:owned"))
        self.assertEqual("unit message\n", self.g(self.tree, "show", "HEAD:checkpoint-message"))

    def test_external_cwd_user_does_not_veto_removal(self):
        job = subprocess.Popen([sys.executable, "-c", 'import sys;print("ready",flush=True);sys.stdin.readline()'],
            cwd=self.tree, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.jobs.append(job)
        self.jobs_settled = False
        self.assertEqual("ready\n", job.stdout.readline())
        self.remove()
        self.assertFalse(self.tree.exists())
        self.assertIsNone(job.poll())

    def test_ref_retirement_requires_remote_and_no_attachment(self):
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", self.base, expect=73)
        self.remove()
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", self.base)
        self.assertNotEqual(0, protocol.git(self.main, "show-ref", "--verify",
                                          "refs/heads/" + self.branch, check=False).returncode)

    def test_ambient_git_redirects_cannot_hide_real_index(self):
        alternate = self.root / "alternate-index"
        protocol.git(self.tree, "read-tree", "HEAD", env={"GIT_INDEX_FILE": str(alternate)})
        (self.tree / "owned").write_text("staged recovery\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("original\n")
        environment = dict(os.environ, GIT_INDEX_FILE=str(alternate), GIT_DIR=str(self.remote),
                           GIT_WORK_TREE=str(self.main), GIT_NAMESPACE="other")
        self.assertIn("owned", self.g(self.tree, "diff", "--cached", "--name-only"))
        self.run_protocol("reuse", "--path", self.tree, "--branch", self.branch, "--base", self.base,
                          env=environment)
        self.run_protocol("remove", "--names", "tree", env=environment)
        self.assertFalse(self.tree.exists())

    def test_observed_identity_drift_preserved(self):
        expected = json.dumps(dict(path=str(self.tree), head="0" * 40, branch="refs/heads/" + self.branch))
        self.remove(73, "--expected", expected)
        self.assertTrue(self.tree.exists())

    def paused_job(self, operation, *arguments):
        bin_path = self.root / "bin"
        bin_path.mkdir(exist_ok=True)
        ready = self.root / "ready.fifo"
        release = self.root / "release.fifo"
        os.mkfifo(ready)
        os.mkfifo(release)
        real_git = shutil.which("git")
        shim = bin_path / "git"
        shim.write_text(f'''#!{sys.executable}
import os,sys
if {operation!r} in sys.argv:
    open({str(self.root / 'native.pid')!r},"w").write(str(os.getpid()))
    with open({str(ready)!r},"w") as output: output.write("ready\\n")
    with open({str(release)!r}) as input: input.readline()
    error=os.open({str(self.root / 'native.stderr')!r},os.O_CREAT|os.O_WRONLY,0o600); os.dup2(error,2)
os.execv({real_git!r}, [{real_git!r}] + sys.argv[1:])
''')
        shim.chmod(0o755)
        reader = os.open(ready, os.O_RDONLY | os.O_NONBLOCK)
        self.addCleanup(os.close, reader)
        env = dict(os.environ, PATH=str(bin_path) + os.pathsep + os.environ["PATH"])
        job = subprocess.Popen([sys.executable, "-B", str(SCRIPT), "--source", str(self.main), *map(str, arguments)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, text=True)
        self.jobs.append(job)
        self.jobs_settled = False
        self.note("pause.readiness.begin", command=job.args, native_pid=job.pid, operation=operation, guard_seconds=20)
        self.assertTrue(select.select([reader], [], [], 20)[0], "paused command readiness timeout")
        self.assertEqual(b"ready\n", os.read(reader, 100))
        self.note("pause.readiness.end", native_pid=job.pid, descendant_pid=int((self.root / "native.pid").read_text()))
        return job, release

    def test_checkpoint_git_scope_releases_after_native_commit(self):
        (self.tree / "owned").write_text("snapshot\n")
        message = self.root / "message"
        message.write_text("ordinary unit\n")
        job, release = self.paused_job("commit", "checkpoint", "--path", self.tree,
            "--message-file", message)
        self.run_protocol("with", "--path", self.tree, "--git", "--", "true", expect=73)
        self.run_protocol("with", "--path", self.tree, "--write", "other", "--", "true")
        with release.open("w") as output:
            output.write("continue\n")
        stdout, stderr = job.communicate(timeout=20)
        self.assertEqual(0, job.returncode, stdout + stderr)
        self.run_protocol("with", "--path", self.tree, "--git", "--", "true")

    def test_removal_does_not_acquire_participation_exclusion(self):
        job, release = self.paused_job("remove", "remove", "--names", "tree")
        self.run_protocol("with", "--path", self.tree, "--", "true")
        with release.open("w") as output:
            output.write("continue\n")
        stdout, stderr = job.communicate(timeout=20)
        self.assertEqual(0, job.returncode, stdout + stderr)
        self.assertFalse(self.tree.exists())

    def test_killed_remover_reports_no_publication_and_native_child_can_finish(self):
        job, release = self.paused_job("remove", "remove", "--names", "tree")
        native_pid = int((self.root / "native.pid").read_text())
        if hasattr(os, "pidfd_open"):
            handle = os.pidfd_open(native_pid)
            self.addCleanup(os.close, handle)
            wait_native = lambda: select.select([handle], [], [], 20)[0]
        else:
            handle = select.kqueue()
            self.addCleanup(handle.close)
            handle.control([select.kevent(native_pid, filter=select.KQ_FILTER_PROC,
                flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT, fflags=select.KQ_NOTE_EXIT)], 0, 0)
            wait_native = lambda: handle.control([], 1, 20)
        try:
            job.kill()
            job.wait(timeout=10)
            self.run_protocol("with", "--path", self.tree, "--", "true")
            with release.open("w") as output:
                output.write("continue\n")
            self.assertTrue(wait_native(), "native process completion timeout")
            job.communicate(timeout=20)
            self.assertFalse(self.tree.exists(), (self.root / "native.stderr").read_text())
        finally:
            try:
                os.kill(native_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    def test_host_join_finalization_and_other_participant(self):
        writer = self.hold("--write", "owned")
        other = self.hold("--write", "other")
        args = ["finalize", "--path", self.tree, "--branch", self.branch]
        self.run_protocol(*args, expect=73)
        writer.communicate("joined\n", timeout=10)
        self.run_protocol(*args, "--writers-joined")
        self.assertIsNone(other.poll())
        self.remove()
        self.assertIsNone(other.poll())

    def runlocal_consumer(self):
        root = self.workspace("worktree-runlocal-", "/tmp")
        dirty, snapshot, unknown = root / "dirty", root / "snapshot", root / "unknown"
        self.g(self.main, "worktree", "add", "-b", "runlocal-recovery", dirty, self.base)
        (dirty / "owned").write_text("unpublished recovery\n")
        snapshot.mkdir()
        (snapshot / "owned").write_text("original\n")
        unknown.mkdir()
        (unknown / "private").write_text("private recovery\n")
        artifact = root / "artifact"
        artifact.write_text("unconfirmed file\n")
        container = root / "container"
        nested = container / "registered"
        self.g(self.main, "worktree", "add", "--detach", nested, self.base)
        self.g(self.main, "worktree", "lock", nested)
        targets = [dirty, snapshot, unknown, artifact]
        aged = time.time() - 3600
        for target in [*targets, container]:
            for path in ([*target.rglob("*"), target] if target.is_dir() else [target]):
                os.utime(path, (aged, aged))
        recent = root / "recent"
        recent.write_text("recent artifact\n")
        alias = root / "alias"
        alias.symlink_to(artifact)
        manifest = root / "manifest.json"
        manifest.write_text(json.dumps(dict(paths=list(map(str, [*targets, recent, alias, root, container])))))
        self.g(self.main, "remote", "remove", "origin")
        command = ["/bin/bash", str(ROOT / "tools/scripts/agent/clean-runlocal.sh"), "--manifest", str(manifest),
            "--root", str(root), "--source", str(self.main), "--base", self.base, "--min-age-min", "15"]
        preview = self.run_owned_command(command, self.root, phase="runlocal-preview", timeout=30, check=False)
        self.assertEqual(0, preview.returncode, preview.stdout + preview.stderr)
        self.assertEqual(list(map(str, targets)), json.loads(preview.stdout)["would_remove"])
        self.assertTrue(all(path.exists() for path in targets))
        result = self.run_owned_command([*command, "--delete"], self.root, phase="runlocal", timeout=30, check=False)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(list(map(str, [dirty, snapshot, unknown, artifact])), json.loads(result.stdout)["removed"])
        self.assertFalse(snapshot.exists())
        self.assertFalse(dirty.exists())
        self.assertFalse(unknown.exists())
        self.assertFalse(artifact.exists())
        self.assertEqual("recent artifact\n", recent.read_text())
        self.assertTrue(alias.is_symlink())
        self.assertTrue(root.exists())
        self.assertTrue(nested.exists())
        self.assertEqual("nested_worktree", json.loads(result.stdout)["entries"][-1]["reason"])

    def initializer_lifetime(self, cli=None):
        cli = cli or self.initializer_cli
        # Exercise the production .NET launcher, not just Python fork/exec.
        (self.main / "lake-manifest.json").write_bytes((ROOT / "lake-manifest.json").read_bytes())
        self.g(self.main, "add", "lake-manifest.json")
        self.g(self.main, "commit", "-m", "initializer pins")
        target = self.root / "initializing"
        binary = self.root / "bin"
        binary.mkdir()
        ready, release = self.root / "ready.fifo", self.root / "release.fifo"
        os.mkfifo(ready)
        os.mkfifo(release)
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!{sys.executable}
import os,sys
if "worktree" in sys.argv and "add" in sys.argv:
    open({str(self.root / 'native.pid')!r},"w").write(str(os.getpid()))
    with open({str(ready)!r},"w") as output: output.write("ready\\n")
    with open({str(release)!r}) as input: input.readline()
    output=os.open({str(self.root / 'native.output')!r},os.O_CREAT|os.O_WRONLY,0o600)
    os.dup2(output,1); os.dup2(output,2)
os.execv({real_git!r},[{real_git!r}]+sys.argv[1:])
''')
        shim.chmod(0o755)
        reader = os.open(ready, os.O_RDONLY | os.O_NONBLOCK)
        self.addCleanup(os.close, reader)
        job = subprocess.Popen(["dotnet", cli, "worktree", "--kind", "governance", "--name", "initializer-lifetime",
            "--path", str(target), "--source", str(self.main), "--base", "HEAD", "--skip-restore"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"]))
        self.jobs.append(job)
        self.jobs_settled = False
        self.assertTrue(select.select([reader], [], [], 20)[0], "native initializer readiness timeout")
        self.assertEqual(b"ready\n", os.read(reader, 100))
        native_pid = int((self.root / "native.pid").read_text())
        if hasattr(os, "pidfd_open"):
            handle = os.pidfd_open(native_pid)
            self.addCleanup(os.close, handle)
            wait_native = lambda: select.select([handle], [], [], 20)[0]
        else:
            handle = select.kqueue()
            self.addCleanup(handle.close)
            handle.control([select.kevent(native_pid, filter=select.KQ_FILTER_PROC,
                flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT, fflags=select.KQ_NOTE_EXIT)], 0, 0)
            wait_native = lambda: handle.control([], 1, 20)
        try:
            job.kill()
            job.wait(timeout=10)
            result = self.run_protocol("with", "--path", target, "--", "true", expect=73)
            self.assertIn("busy_scope", result.stderr)
            with release.open("w") as output:
                output.write("continue\n")
            self.assertTrue(wait_native(), "native initializer completion timeout")
            stdout, stderr = job.communicate(timeout=20)
            self.assertTrue(target.is_dir(), stdout + stderr + (self.root / "native.output").read_text())
            metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
            self.assertTrue((metadata / "locked").read_text().startswith("worktree-init:"))
            self.run_protocol("with", "--path", target, "--", "true")
        finally:
            try:
                os.kill(native_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


if __name__ == "__main__":
    NativeFixture.install_interrupt_handler()
    if len(sys.argv) == 3 and sys.argv[1] == "--initializer":
        fixture = ProtocolTests("initializer_lifetime")
        fixture.initializer_cli = sys.argv[2]
        result = unittest.TextTestRunner(verbosity=2).run(fixture)
        sys.exit(0 if result.wasSuccessful() else 1)
    else:
        unittest.main(verbosity=2)
