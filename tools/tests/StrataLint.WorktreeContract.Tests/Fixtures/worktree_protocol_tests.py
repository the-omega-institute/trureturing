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

ROOT = Path(sys.argv.pop(1)).resolve()
SCRIPT = ROOT / "tools/scripts/worktree/worktree_protocol.py"
sys.path.insert(0, str(SCRIPT.parent))
import worktree_protocol as protocol
import worktree_preservation as preservation


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="worktree-contract-")
        self.addCleanup(self.cleanup_fixture)
        self.root = Path(self.temp.name).resolve()
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

    def cleanup_fixture(self):
        result = self._outcome.result if self._outcome else None
        failed = (any(test is self or getattr(test, "test_case", None) is self
                      for test, _ in result.failures + result.errors) if result is not None
                  else sys.exc_info()[0] is not None or self._outcome is not None and not self._outcome.success)
        if failed:
            # Failed input is recovery evidence, including when a cleanup fails.
            self.temp._finalizer.detach()
            self.note("fixture.retained", reason="failed probe or native settlement")
        else:
            self.temp.cleanup()
            self.note("fixture.cleaned")

    def stop_jobs(self):
        for job in self.jobs:
            self.note("job.settle.begin", native_pid=job.pid, returncode=job.poll())
            if job.poll() is None:
                job.kill()
            job.communicate(timeout=10)
            self.note("job.settle.end", native_pid=job.pid, returncode=job.returncode)

    def g(self, root, *args):
        command = ["git", "-C", str(root), *map(str, args)]
        start = time.monotonic()
        job = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               env=protocol.git_environment(), pass_fds=protocol.scope_fds())
        self.note("git.begin", command=command, native_pid=job.pid, guard_seconds=300)
        try:
            stdout, stderr = job.communicate(timeout=300)
        except subprocess.TimeoutExpired as error:
            self.note("git.guard", native_pid=job.pid, elapsed=time.monotonic() - start,
                      stdout=os.fsdecode(error.output or b""), stderr=os.fsdecode(error.stderr or b""))
            job.kill()
            job.communicate()
            raise
        self.note("git.end", native_pid=job.pid, elapsed=time.monotonic() - start,
                  returncode=job.returncode, stdout=os.fsdecode(stdout), stderr=os.fsdecode(stderr))
        if job.returncode:
            raise protocol.Refused(os.fsdecode(stderr).strip() or "git failed")
        return os.fsdecode(stdout)

    def run_protocol(self, *args, expect=0, env=None):
        command = [sys.executable, "-B", str(SCRIPT), "--source", str(self.main), *map(str, args)]
        start = time.monotonic()
        job = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
        self.note("protocol.begin", command=command, native_pid=job.pid, guard_seconds=30)
        try:
            stdout, stderr = job.communicate(timeout=30)
        except subprocess.TimeoutExpired as error:
            self.note("protocol.guard", native_pid=job.pid, elapsed=time.monotonic() - start,
                      stdout=os.fsdecode(error.output or b""), stderr=os.fsdecode(error.stderr or b""))
            job.kill()
            job.communicate()
            raise
        self.note("protocol.end", native_pid=job.pid, elapsed=time.monotonic() - start,
                  returncode=job.returncode, stdout=stdout, stderr=stderr)
        self.assertEqual(expect, job.returncode, stdout + stderr)
        return subprocess.CompletedProcess(command, job.returncode, stdout, stderr)

    def hold(self, *scopes, code=None):
        code = code or 'import sys; print("ready",flush=True); sys.stdin.readline()'
        job = subprocess.Popen([sys.executable, "-B", str(SCRIPT), "--source", str(self.main),
            "with", "--path", str(self.tree), *scopes, "--", sys.executable, "-c", code],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.jobs.append(job)
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
        return self.run_protocol("checkpoint", "--path", self.tree, "--write", "owned",
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

    def test_attributed_checkpoint_excludes_staged_and_allows_other_editor(self):
        self.hold("--write", "other")
        (self.tree / "other").write_text("unrelated staged\n")
        self.g(self.tree, "add", "other")
        (self.tree / "owned").write_text("authorized\n")
        self.checkpoint()
        self.assertEqual("authorized\n", self.g(self.tree, "show", "HEAD:owned"))
        self.assertEqual("original\n", self.g(self.tree, "show", "HEAD:other"))
        self.assertEqual("other\n", self.g(self.tree, "diff", "--cached", "--name-only"))

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

    def test_checkpoint_failure_retains_private_index_and_source(self):
        (self.tree / "owned").write_text("authorized\n")
        message = self.root / "message"
        message.write_text("authorized unit\n")
        binary = self.root / "failure-shim"
        binary.mkdir()
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!{sys.executable}
import os,sys
if "commit-tree" in sys.argv: raise SystemExit(1)
os.execv({real_git!r},[{real_git!r}]+sys.argv[1:])
''')
        shim.chmod(0o755)
        environment = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"])
        self.run_protocol("checkpoint", "--path", self.tree, "--write", "owned", "--message-file", message,
                          expect=73, env=environment)
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        self.assertEqual(1, len(list(metadata.glob("checkpoint-index-*"))))
        self.assertEqual("authorized\n", (self.tree / "owned").read_text())
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())

    def test_clean_remote_preserved_removal_and_main_protection(self):
        self.remove()
        self.assertFalse(self.tree.exists())
        self.run_protocol("remove", "--names", "main", expect=73)

    def test_nested_directory_qualification_preserves_nonempty_prefix_sibling(self):
        tracked = self.tree / "deep" / "branch" / "leaf.txt"
        tracked.parent.mkdir(parents=True)
        tracked.write_text("retained nested content\n")
        self.g(self.tree, "add", "deep/branch/leaf.txt")
        self.g(self.tree, "commit", "-m", "nested retained content")
        self.g(self.tree, "push", "origin", self.branch)
        unknown = self.tree / "deep" / "branch-extra" / "private"
        unknown.parent.mkdir()
        unknown.write_text("unpublished recovery\n")
        result = self.remove(73)
        self.assertIn("unknown_directory:", result.stderr)
        self.assertEqual("unpublished recovery\n", unknown.read_text())
        unknown.unlink()
        # Empty untracked directories carry no bytes; all tracked ancestors remain.
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_busy_and_new_entry_exclusion(self):
        self.hold()
        self.remove(73)
        self.assertTrue(self.tree.exists())

    def test_dirty_untracked_ignored_and_staged_preserved(self):
        for name in ("owned", "untracked", ".private"):
            file = self.tree / name
            before = file.read_bytes() if file.exists() else None
            file.write_text("recovery\n")
            self.remove(73)
            self.assertEqual("recovery\n", file.read_text())
            if before is None:
                file.unlink()
            else:
                file.write_bytes(before)
        (self.tree / "owned").write_text("staged\n")
        self.g(self.tree, "add", "owned")
        self.remove(73)

    def test_local_only_and_private_history_preserved(self):
        (self.tree / "owned").write_text("local\n")
        self.checkpoint()
        self.remove(73)
        local = self.g(self.tree, "rev-parse", "HEAD").strip()
        self.g(self.tree, "reset", "--hard", self.base)
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "ORIG_HEAD").write_text(local + "\n")
        self.remove(73)

    def test_unknown_operation_and_cache_guard_preserved(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "MERGE_HEAD").write_text(self.base + "\n")
        self.remove(73)
        (metadata / "MERGE_HEAD").unlink()
        with ExitStack() as stack:
            preservation.cache_exclusion(stack, self.tree)
            self.remove(73)

    def test_whole_batch_preflight_preserves_eligible_member(self):
        other = self.root / "second"
        self.g(self.main, "worktree", "add", "--detach", other, "HEAD")
        (other / "private").write_text("unknown\n")
        self.run_protocol("remove", "--names", "tree second", expect=73)
        self.assertTrue(self.tree.exists())

    def test_native_partial_removal_reports_actual_effects_and_continues(self):
        second = self.root / "second"
        self.g(self.main, "worktree", "add", "--detach", second, "HEAD")
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
        self.remove(73)
        (self.tree / "private-output").unlink()
        oid = self.g(self.tree, "rev-parse", "HEAD:owned").strip()
        protocol.git(self.tree, "update-index", "--index-info",
                     input=f"100644 {oid} 1\towned\n100644 {oid} 2\towned\n".encode())
        self.remove(73)
        self.assertTrue(self.g(self.tree, "ls-files", "--unmerged"))

    def recovery_clean_index_with_resolved_conflict_is_preserved(self):
        oid = self.g(self.tree, "rev-parse", "HEAD:owned").strip()
        protocol.git(self.tree, "update-index", "--index-info",
                     input=f"0 {'0' * len(oid)}\towned\n100644 {oid} 1\towned\n100644 {oid} 2\towned\n".encode())
        (self.tree / "owned").write_text("resolved\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("original\n")
        self.g(self.tree, "add", "owned")
        self.assertEqual("", self.g(self.tree, "status", "--porcelain"))
        self.assertTrue(self.g(self.tree, "ls-files", "--resolve-undo"))
        self.assertIn("resolve_undo_recovery", self.remove(73).stderr)
        self.assertTrue(self.tree.exists())

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
        self.remove(73)
        self.assertEqual("local recovery\n", (self.tree / "owned").read_text())
        self.g(self.main, "worktree", "remove", self.tree)
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", local, expect=73)
        self.assertEqual(local, self.g(self.main, "rev-parse", "refs/heads/" + self.branch).strip())

    def recovery_checkpoint_protects_input_reads(self):
        (self.tree / "owned").write_text("authorized\n")
        input_file = self.tree / "checkpoint-input"
        input_file.write_text("unit message\n")
        writer = self.hold("--write", input_file.name)
        self.checkpoint("--message-file", input_file, expect=73)
        input_file.write_bytes(b"owned\0")
        message = self.root / "message"
        message.write_text("unit message\n")
        self.run_protocol("checkpoint", "--path", self.tree, "--paths-from", input_file,
                          "--message-file", message, expect=73)
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        writer.communicate("joined\n", timeout=10)
        self.run_protocol("checkpoint", "--path", self.tree, "--paths-from", input_file,
                          "--message-file", message)
        self.assertEqual("authorized\n", self.g(self.tree, "show", "HEAD:owned"))
        self.assertNotEqual(0, protocol.git(self.tree, "cat-file", "-e", "HEAD:checkpoint-input", check=False).returncode)

    def test_external_cwd_user_is_preserved(self):
        job = subprocess.Popen([sys.executable, "-c", 'import sys;print("ready",flush=True);sys.stdin.readline()'],
            cwd=self.tree, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.jobs.append(job)
        self.assertEqual("ready\n", job.stdout.readline())
        result = self.remove(73)
        self.assertIn("host_activity", result.stderr)

    def test_ref_retirement_requires_remote_and_no_attachment(self):
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", self.base, expect=73)
        self.remove()
        self.run_protocol("retire-branch", "--branch", self.branch, "--commit", self.base)
        self.assertNotEqual(0, protocol.git(self.main, "show-ref", "--verify",
                                          "refs/heads/" + self.branch, check=False).returncode)

    def test_snapshot_matches_remote_bytes_and_preserves_unknown(self):
        snapshot = self.root / "snapshot"
        snapshot.mkdir()
        (snapshot / "owned").write_text("original\n")
        (snapshot / "extra").write_text("unpublished\n")
        args = ["remove-snapshot", "--path", snapshot, "--base", self.base]
        self.run_protocol(*args, expect=73)
        (snapshot / "extra").unlink()
        self.run_protocol(*args)
        self.assertFalse(snapshot.exists())

    def test_ambient_git_redirects_cannot_hide_real_index(self):
        alternate = self.root / "alternate-index"
        protocol.git(self.tree, "read-tree", "HEAD", env={"GIT_INDEX_FILE": str(alternate)})
        (self.tree / "owned").write_text("staged recovery\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("original\n")
        environment = dict(os.environ, GIT_INDEX_FILE=str(alternate), GIT_DIR=str(self.remote),
                           GIT_WORK_TREE=str(self.main), GIT_NAMESPACE="other")
        self.run_protocol("remove", "--names", "tree", env=environment, expect=73)
        self.assertIn("owned", self.g(self.tree, "diff", "--cached", "--name-only"))
        self.run_protocol("reuse", "--path", self.tree, "--branch", self.branch, "--base", self.base,
                          env=environment)

    def test_snapshot_root_alias_and_observed_identity_drift_preserved(self):
        snapshot = self.root / "snapshot"
        snapshot.mkdir()
        (snapshot / "owned").write_text("original\n")
        alias = self.root / "alias"
        alias.symlink_to(snapshot, target_is_directory=True)
        self.run_protocol("remove-snapshot", "--path", alias, "--base", self.base, expect=73)
        self.assertTrue(snapshot.exists())
        expected = json.dumps(dict(path=str(self.tree), head="0" * 40, branch="refs/heads/" + self.branch))
        self.remove(73, "--expected", expected)
        self.assertTrue(self.tree.exists())

    def test_mirror_operation_publishes_then_qualifies_removal(self):
        self.g(self.main, "switch", "-c", "feature")
        (self.main / "feature").write_text("feature\n")
        self.g(self.main, "add", "feature")
        self.g(self.main, "commit", "-m", "feature")
        feature = self.g(self.main, "rev-parse", "HEAD").strip()
        mirror = self.root / "mirror-tree"
        branch = "mirror/integration/11"
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", branch, "--base", self.base,
                          "--merge", feature, "--message", "mirror: feature")
        self.assertEqual("feature\n", self.g(mirror, "show", "HEAD:feature"))
        self.run_protocol("remove", "--names", mirror.name)
        self.assertFalse(mirror.exists())

    def test_mirror_failure_retains_conflict_and_failed_publication(self):
        self.g(self.main, "switch", "-c", "feature")
        (self.main / "owned").write_text("feature\n")
        self.g(self.main, "commit", "-am", "feature")
        feature = self.g(self.main, "rev-parse", "HEAD").strip()
        self.g(self.main, "switch", "dev")
        (self.main / "owned").write_text("integration\n")
        self.g(self.main, "commit", "-am", "integration")
        base = self.g(self.main, "rev-parse", "HEAD").strip()
        mirror = self.root / "mirror-conflict"
        self.run_protocol("prepare-mirror", "--path", mirror, "--branch", "mirror/conflict/11", "--base", base,
                          "--merge", feature, "--message", "mirror: conflict", expect=73)
        self.assertTrue(self.g(mirror, "ls-files", "--unmerged"))
        self.run_protocol("remove", "--names", mirror.name, expect=73)
        failed = self.root / "mirror-offline"
        self.g(self.main, "remote", "set-url", "origin", self.root / "missing.git")
        self.run_protocol("prepare-mirror", "--path", failed, "--branch", "mirror/offline/11", "--base", self.base,
                          "--merge", feature, "--message", "mirror: offline", expect=73)
        self.assertEqual("feature\n", (failed / "owned").read_text())

    def consumer_mirror_uses_real_git_with_stubbed_github(self):
        self.g(self.main, "push", "origin", self.base + ":refs/heads/integration-tests")
        self.g(self.main, "switch", "-c", "feature")
        (self.main / "feature").write_text("feature\n")
        self.g(self.main, "add", "feature")
        self.g(self.main, "commit", "-m", "feature")
        self.g(self.main, "switch", "dev")
        self.g(self.main, "merge", "--no-ff", "-m", "Merge pull request #11 from fixture/feature", "feature")
        self.g(self.main, "push", "origin", "dev")
        binary = self.root / "github-stub"
        binary.mkdir()
        gh = binary / "gh"
        gh.write_text(f'''#!{sys.executable}
import json,subprocess,sys
a=sys.argv[1:]
if a[:2]==["auth","status"]: pass
elif a[:2]==["repo","view"]: print("fixture/repo")
elif a[0]=="api": print(json.dumps(dict(protected=True,protection=dict(required_status_checks=dict(contexts=["required"])))))
elif a[:2]==["pr","list"]: print("[]")
elif a[:2]==["pr","create"]: print("https://example.invalid/fixture/repo/pull/17")
elif a[:2]==["pr","checks"]:
    if "--json" in a: print(json.dumps([dict(name="required",bucket="pass")]))
elif a[:2]==["pr","merge"]:
    subprocess.run(["git","push","origin","refs/heads/mirror/integration-tests/11:refs/heads/integration-tests"],check=True)
elif a[:3]==["pr","view","11"]: print(json.dumps(dict(title="feature",url="https://example.invalid/fixture/repo/pull/11")))
elif a[:3]==["pr","view","17"]: print(json.dumps(dict(state="MERGED",mergedAt="2030-01-01T00:00:00Z")))
else: raise SystemExit("unexpected GitHub fixture call: "+repr(a))
''')
        gh.chmod(0o755)
        temporary = self.root / "scratch"
        temporary.mkdir()
        environment = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], TMPDIR=str(temporary))
        script = ROOT / "tools/scripts/agent/integration-mirror.sh"
        result = subprocess.run(["/bin/bash", str(script), "--integration", "integration-tests", "--since", self.base],
            cwd=self.tree, env=environment, capture_output=True, text=True, timeout=60)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn("MIRROR_RESULT mirrored=1 pending=0 exit=0", result.stdout)
        self.assertFalse(list(temporary.iterdir()))
        self.assertEqual("feature\n", self.g(self.main, "show", "refs/remotes/origin/dev:feature"))

    def consumer_land_attributes_paths_with_external_checks_stubbed(self):
        (self.tree / "other").write_text("unrelated staged\n")
        self.g(self.tree, "add", "other")
        paths = self.root / "authorized.paths"
        paths.write_bytes(b"owned\0")
        message = self.root / "unit.msg"
        message.write_text("authorized unit\n")
        binary = self.root / "land-stub"
        binary.mkdir()
        calls = self.root / "make-calls.jsonl"
        for name, body in dict(dotnet='exit 0', gh='echo true').items():
            file = binary / name
            file.write_text("#!/bin/sh\n" + body + "\n")
            file.chmod(0o755)
        make = binary / "make"
        make.write_text(f'''#!{sys.executable}
import json,os,sys
with open({str(calls)!r},"a") as output: output.write(json.dumps(sys.argv[1:])+"\\n")
if sys.argv[1]=="cover" and sys.argv[2]=="ATOM_ID=atom-failure": raise SystemExit(19)
if sys.argv[1]=="pr-open": print("pr=17")
elif sys.argv[1] not in ("lean-report","cover","gate"): raise SystemExit(99)
''')
        make.chmod(0o755)
        environment = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
                           LAND_LOG_DIR=str(self.root / "land-logs"))
        # Exact argument values also distinguish literal backslash-t from a tab.
        one = [("atom-one", "D5/S3/ConceptDynamics.Result")]
        multiple = [("atom-tab\tvalue", "gid with space"), (r"atom-literal\tvalue", r"gid-literal\tvalue")]
        failing = [one[0], ("atom-failure", "D5/S3/ConceptDynamics.Failure"), multiple[0]]
        for index, covers in enumerate(([], one, multiple, failing)):
            with self.subTest(covers=covers):
                owned = f"authorized {index}\n"
                (self.tree / "owned").write_text(owned)
                before = self.g(self.tree, "rev-parse", "HEAD").strip()
                calls.write_text("")
                arguments = [arg for pair in covers for arg in ("--cover", *pair)]
                relative = index == 1
                command = ["/bin/bash", str(ROOT / "tools/scripts/agent/land.sh"),
                    "tree" if relative else str(self.tree), self.branch,
                    message.name if relative else str(message), "--paths-from",
                    paths.name if relative else str(paths), "--wait-pr", "11", *arguments]
                self.note("land.begin", command=command, guard_seconds=60)
                start = time.monotonic()
                result = subprocess.run(command, cwd=self.root if relative else self.main, env=environment,
                    capture_output=True, text=True, timeout=60)
                recorded = [json.loads(line) for line in calls.read_text().splitlines()]
                self.note("land.end", elapsed=time.monotonic() - start, returncode=result.returncode,
                    make_calls=recorded, claimed_merged="PHASE1_MERGED" in result.stdout)
                expected_covers = covers[:2] if covers == failing else covers
                self.assertEqual([["cover", "ATOM_ID=" + atom, "GID=" + gid] for atom, gid in expected_covers],
                                 [call for call in recorded if call[0] == "cover"], result.stdout + result.stderr)
                if covers == failing:
                    self.assertEqual(93, result.returncode, result.stdout + result.stderr)
                    self.assertEqual(["lean-report", "cover", "cover"], [call[0] for call in recorded])
                    self.assertNotIn("PHASE1_MERGED", result.stdout)
                    self.assertEqual(before, self.g(self.tree, "rev-parse", "HEAD").strip())
                    self.assertEqual(owned, (self.tree / "owned").read_text())
                else:
                    self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                    self.assertIn("WAITED_PR=11", result.stdout)
                    self.assertIn("PHASE1_MERGED", result.stdout)
                    self.assertEqual(owned, self.g(self.tree, "show", "HEAD:owned"))
                self.assertEqual("original\n", self.g(self.tree, "show", "HEAD:other"))
                self.assertEqual("unrelated staged\n", (self.tree / "other").read_text())
                self.assertEqual("other\n", self.g(self.tree, "diff", "--cached", "--name-only"))
                self.assertEqual(self.g(self.tree, "rev-parse", "HEAD").strip(),
                                 self.g(self.main, "ls-remote", "origin", "refs/heads/" + self.branch).split()[0])

    def consumer_land_cannot_build_during_native_destruction(self):
        (self.main / ".git/info/exclude").write_text("tools/obj/\n")
        paths = self.root / "authorized.paths"
        paths.write_bytes(b"owned\0")
        message = self.root / "unit.msg"
        message.write_text("authorized unit\n")
        binary = self.root / "land-stub"
        binary.mkdir()
        dotnet = binary / "dotnet"
        material = self.tree / "tools/obj/entry-probe"
        dotnet.write_text(f'''#!{sys.executable}
from pathlib import Path
material=Path({str(material)!r})
material.parent.mkdir(parents=True,exist_ok=True)
material.write_text("new build material\\n")
''')
        dotnet.chmod(0o755)
        environment = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
                           LAND_LOG_DIR=str(self.root / "land-logs"))
        job, release = self.paused_job("remove", "remove", "--names", "tree")
        try:
            result = subprocess.run(["/bin/bash", str(ROOT / "tools/scripts/agent/land.sh"), str(self.tree),
                self.branch, str(message), "--paths-from", str(paths)], cwd=self.main, env=environment,
                capture_output=True, text=True, timeout=60)
            self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn("busy_scope:tree:", result.stderr)
            self.assertNotIn("PHASE1_MERGED", result.stdout)
            self.note("land.excluded", returncode=result.returncode, material_created=material.exists(),
                      claimed_merged="PHASE1_MERGED" in result.stdout)
            self.assertFalse(material.exists(), "landing built the target while destruction held entry")
        finally:
            with release.open("w") as output:
                output.write("continue\n")
            stdout, stderr = job.communicate(timeout=20)
        self.assertEqual(0, job.returncode, stdout + stderr)
        self.assertFalse(self.tree.exists())

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
        self.note("pause.readiness.begin", command=job.args, native_pid=job.pid, operation=operation, guard_seconds=20)
        self.assertTrue(select.select([reader], [], [], 20)[0], "paused command readiness timeout")
        self.assertEqual(b"ready\n", os.read(reader, 100))
        self.note("pause.readiness.end", native_pid=job.pid, descendant_pid=int((self.root / "native.pid").read_text()))
        return job, release

    def test_concurrent_native_staging_cannot_enter_checkpoint(self):
        (self.tree / "owned").write_text("authorized\n")
        message = self.root / "message"
        message.write_text("authorized unit\n")
        job, release = self.paused_job("commit-tree", "checkpoint", "--path", self.tree,
            "--write", "owned", "--message-file", message)
        (self.tree / "other").write_text("concurrently staged\n")
        self.g(self.tree, "add", "other")
        with release.open("w") as output:
            output.write("continue\n")
        stdout, stderr = job.communicate(timeout=20)
        self.assertEqual(0, job.returncode, stdout + stderr)
        self.assertEqual("original\n", self.g(self.tree, "show", "HEAD:other"))
        self.assertEqual("other\n", self.g(self.tree, "diff", "--cached", "--name-only"))

    def test_entry_is_excluded_through_native_destruction(self):
        job, release = self.paused_job("remove", "remove", "--names", "tree")
        self.run_protocol("with", "--path", self.tree, "--", "true", expect=73)
        self.run_protocol("with", "--path", self.tree / "nested", "--", "true", expect=73)
        with release.open("w") as output:
            output.write("continue\n")
        stdout, stderr = job.communicate(timeout=20)
        self.assertEqual(0, job.returncode, stdout + stderr)
        self.assertFalse(self.tree.exists())

    def test_killed_remover_keeps_surviving_native_child_exclusion(self):
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
            self.run_protocol("with", "--path", self.tree, "--", "true", expect=73)
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
        self.remove(73)

    def runlocal_consumer(self):
        with tempfile.TemporaryDirectory(prefix="worktree-runlocal-", dir="/tmp") as directory:
            root = Path(directory)
            dirty, snapshot, unknown = root / "dirty", root / "snapshot", root / "unknown"
            self.g(self.main, "worktree", "add", "--detach", dirty, self.base)
            (dirty / "owned").write_text("unpublished recovery\n")
            snapshot.mkdir()
            (snapshot / "owned").write_text("original\n")
            unknown.mkdir()
            (unknown / "private").write_text("private recovery\n")
            artifact = root / "artifact"
            artifact.write_text("unconfirmed file\n")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps(dict(paths=list(map(str, [dirty, snapshot, unknown, artifact])))))
            command = ["/bin/bash", str(ROOT / "tools/scripts/agent/clean-runlocal.sh"), "--manifest", str(manifest),
                "--root", str(root), "--source", str(self.main), "--base", self.base, "--min-age-min", "0", "--delete"]
            result = subprocess.run(command, capture_output=True, text=True, timeout=30)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertEqual([str(snapshot)], json.loads(result.stdout)["removed"])
            self.assertFalse(snapshot.exists())
            self.assertEqual("unpublished recovery\n", (dirty / "owned").read_text())
            self.assertEqual("private recovery\n", (unknown / "private").read_text())
            self.assertEqual("unconfirmed file\n", artifact.read_text())

    def initializer_lifetime(self, cli):
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
    if len(sys.argv) == 3 and sys.argv[1] == "--initializer":
        fixture = ProtocolTests("test_cross_session_dirty_reuse_preserves_bytes")
        fixture.setUp()
        try:
            fixture.initializer_lifetime(sys.argv[2])
        finally:
            fixture.doCleanups()
    else:
        unittest.main(verbosity=2)
