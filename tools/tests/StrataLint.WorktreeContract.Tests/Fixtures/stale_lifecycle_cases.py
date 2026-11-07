"""Disposable Git checks for the age/stale worktree lifecycle."""
import os
import fcntl
import json
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(sys.argv.pop(1)).resolve()
sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
import worktree_protocol as protocol
import worktree_pool as pool


def run(cwd, *args, env=None, check=True):
    result = subprocess.run(["git", "-C", str(cwd), *map(str, args)],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=protocol.git_environment(env), check=False)
    if check and result.returncode:
        raise AssertionError(result.stderr)
    return result


class LifecycleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="stale-lifecycle-")
        self.root = Path(self.tmp.name).resolve()
        self.main = self.root / "main"
        run(self.root, "init", "--bare", self.root / "remote.git")
        run(self.root, "init", "--initial-branch=dev", self.main)
        run(self.main, "config", "user.name", "Lifecycle Tests")
        run(self.main, "config", "user.email", "lifecycle@example.invalid")
        for name in ("lean-toolchain", "lake-manifest.json", "Reg/lakefile.toml",
                     "Reg/lake-manifest.json", "tools/lean-inspector-reg/lakefile.toml",
                     "tools/lean-inspector-reg/lake-manifest.json"):
            target = self.main / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "base")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        self.source = self.main
        run(self.main, "update-ref", "refs/remotes/origin/dev", self.base)

    def tearDown(self):
        self.tmp.cleanup()

    def commit_branch(self, name, path, age, content="branch\n"):
        run(self.main, "branch", name, self.base)
        run(self.main, "worktree", "add", path, name)
        (Path(path) / "payload").write_text(content)
        run(path, "add", "payload")
        stamp = str(int(time.time()) - age)
        run(path, "commit", "-m", "payload", env={"GIT_AUTHOR_DATE": "@" + stamp,
                                                     "GIT_COMMITTER_DATE": "@" + stamp})
        return run(path, "rev-parse", "HEAD").stdout.strip()

    def cli(self, *args, cwd=None, check=True):
        result = subprocess.run([shutil.which("dotnet"), str(ROOT /
            "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"), *map(str, args)],
            cwd=cwd or self.source, text=True, capture_output=True,
            env=protocol.git_environment(), timeout=60)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def create(self, name, path, reuse_any=False, check=True, cwd=None):
        return self.cli("worktree", "--kind", "governance", "--name", name,
                        "--path", path, "--base", self.base, "--skip-restore",
                        *(["--reuse-any"] if reuse_any else []), check=check, cwd=cwd)

    def prepare_make(self):
        # This launcher only replaces dotnet run's build with this test's freshly
        # built CLI. Every lifecycle action and native Git effect is real.
        scripts = self.main / "tools/scripts"
        shutil.copytree(ROOT / "tools/scripts/worktree", scripts / "worktree")
        shutil.copytree(ROOT / "tools/scripts/report", scripts / "report")
        inspector = self.main / "tools/lean-inspector"
        inspector.mkdir()
        for module in (ROOT / "tools/lean-inspector").glob("*.py"):
            shutil.copy2(module, inspector / module.name)
        for name in ("host-cleanup.py", "worktree-init.sh", "clean-lanes.sh", "maintenance_log.py"):
            shutil.copy2(ROOT / "tools/scripts" / name, scripts / name)
        for name in ("Makefile", "tools/Makefile"):
            shutil.copy2(ROOT / name, self.main / name)
        tools = self.main / "tools"
        (tools / "Fixture.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n')
        (tools / "StrataLint.sln").write_text('Microsoft Visual Studio Solution File, Format Version 12.00\n'
            'Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "Fixture", "Fixture.csproj", '
            '"{6375E1CB-330C-4D28-8AE5-861A56749FD9}"\nEndProject\nGlobal\nEndGlobal\n')
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "make entrances")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        launcher = self.bin / "dotnet"
        launcher.write_text('#!/bin/bash\nif [[ "$1" == run ]]; then\n'
            '  while [[ $# -gt 0 && "$1" != -- ]]; do shift; done\n'
            '  [[ $# -gt 0 ]] || exit 64\n  shift\n'
            '  exec "$FRONTDOOR_DOTNET" "$FRONTDOOR_CLI" "$@"\nfi\n'
            'exec "$FRONTDOOR_DOTNET" "$@"\n')
        launcher.chmod(0o755)
        self.env = protocol.git_environment({
            "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
            "FRONTDOOR_DOTNET": shutil.which("dotnet"),
            "FRONTDOOR_CLI": str(ROOT / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"),
            "TMPDIR": str(self.root / "tmp"),
            "CODEX_HOME": str(self.root / "codex"), "SSHX_HOME": str(self.root / "sshx")})
        (self.root / "tmp").mkdir()

    def make(self, *args, cwd=None, check=True):
        result = subprocess.run(["make", "--no-print-directory", *map(str, args)],
                                cwd=cwd or self.main, env=self.env,
                                text=True, capture_output=True, timeout=90)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def options(self, branch, path=None):
        return SimpleNamespace(source=self.source, path=Path(path).resolve() if path else None,
                               branch=branch, base=self.base, skip_restore=True, exclude_path=[])

    def test_stale_reuse_is_immediate_and_new_commit_invalidates(self):
        candidate = self.root / "candidate"
        old_branch = "lane/governance/old"
        head = self.commit_branch(old_branch, candidate, 60)
        marked = protocol.mark_stale(self.source, candidate)
        self.assertEqual(marked["head"], head)
        result = pool.claim(self.options("lane/governance/new"))
        self.assertEqual(result["status"], "claimed", result)
        current = next(row for row in protocol.inventory(self.source)
                       if Path(row["worktree"]).resolve() == candidate.resolve())
        self.assertEqual(current["branch"], "refs/heads/lane/governance/new")
        self.assertEqual(run(self.source, "show-ref", "--verify", "refs/heads/" + old_branch).returncode, 0)

        fresh = self.root / "fresh"
        self.commit_branch("lane/governance/fresh", fresh, 0)
        protocol.mark_stale(self.source, fresh)
        run(fresh, "commit", "--allow-empty", "-m", "new")
        reusable, reason = protocol.reusable(fresh, self.source)
        self.assertFalse(reusable)
        self.assertEqual(reason, "head_recent")

    def test_age_reuse_ignores_legacy_lock_and_live_process(self):
        candidate = self.root / "busy"
        old_branch = "lane/governance/busy"
        self.commit_branch(old_branch, candidate, 5 * 60 * 60)
        metadata = Path(run(candidate, "rev-parse", "--git-dir").stdout.strip())
        (metadata / "locked").write_text("legacy marker\n")
        holder = subprocess.Popen(
            [sys.executable, "-c", "import os,time; os.chdir(os.environ['TREE']); open(os.path.join(os.environ['TREE'],'held'),'wb').close(); time.sleep(30)"],
            env={**os.environ, "TREE": str(candidate)})
        try:
            result = self.create("reused", candidate)
            self.assertEqual(json.loads(result.stdout)["status"], "claimed", result.stdout)
        finally:
            holder.terminate()
            holder.wait(timeout=10)

    def test_strict_boundaries_future_unknown_main_and_direct_removal(self):
        exact4 = self.root / "exact4"
        self.commit_branch("lane/governance/exact4", exact4, 4 * 60 * 60)
        head_time = protocol.head_committer_time(exact4)
        self.assertFalse(protocol.reusable(exact4, self.source, head_time + 4 * 60 * 60)[0])
        self.assertTrue(protocol.reusable(exact4, self.source, head_time + 4 * 60 * 60 + 1)[0])
        self.assertFalse(protocol.reusable(exact4, self.source, head_time - 1)[0])

        old = self.root / "old"
        old_branch = "lane/governance/old-dirty"
        head = self.commit_branch(old_branch, old, 7 * 60 * 60)
        (old / "unfinished").write_text("dirty\n")
        metadata = Path(run(old, "rev-parse", "--git-dir").stdout.strip())
        (metadata / "MERGE_HEAD").write_text(head + "\n")
        result = pool.sweep(self.source, self.base, force=True)
        self.assertTrue(any(row["path"] == str(old.resolve()) and row["outcome"] == "removed" for row in result["items"]))
        self.assertFalse(any(Path(row["worktree"]).resolve() == old.resolve()
                             for row in protocol.inventory(self.source)))
        self.assertEqual(run(self.source, "show-ref", "--verify", "refs/heads/" + old_branch).returncode, 0)
        with self.assertRaises(protocol.Refused):
            protocol.mark_stale(self.source, self.source)

        original = protocol.head_committer_time
        try:
            protocol.head_committer_time = lambda _: (_ for _ in ()).throw(protocol.Refused("head_timestamp_unknown"))
            with self.assertRaises(protocol.Refused):
                protocol.reusable(exact4, self.source)
        finally:
            protocol.head_committer_time = original

    def test_make_default_release_marks_current_branch_with_executable_path_intact(self):
        self.prepare_make()
        tree = self.root / "finished task"
        branch = "lane/governance/finished"
        head = self.commit_branch(branch, tree, 60)
        (tree / "ordinary-untracked").write_text("keep until reassignment")
        for target in ("worktree-stale", "worktree-return"):
            with self.subTest(target=target):
                self.make(target, cwd=tree)
                self.assertEqual(protocol.stale_head(self.main, "refs/heads/" + branch), head)
                run(self.main, "config", "--unset-all", protocol.branch_config_key("refs/heads/" + branch))
        self.make("worktree-stale", "WORKTREE_PATH=" + str(tree))
        self.assertEqual(protocol.stale_head(self.main, "refs/heads/" + branch), head)
        self.assertTrue((tree / "ordinary-untracked").exists())
        self.assertNotEqual(self.make("worktree-stale", check=False).returncode, 0)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_make_custom_attached_task_resumes_immediately_without_destination(self):
        self.prepare_make()
        tree = self.root / "custom session"
        self.make("worktree", "KIND=governance", "NAME=resume", "BASE=" + self.base,
                  "DEST=" + str(tree), "ALLOW_LOW_DISK=1")
        (tree / "lean-toolchain").write_text((self.main / "lean-toolchain").read_text())
        # Ordinary tracked/untracked bytes do not participate in lifecycle eligibility.
        (tree / "tools/Fixture.csproj").write_text("tracked edit\n")
        (tree / "untracked").write_text("untracked bytes\n")
        resumed = self.make("worktree", "KIND=governance", "NAME=resume", "BASE=" + self.base,
                            "ALLOW_LOW_DISK=1")
        self.assertIn('"status": "reused"', resumed.stdout)
        self.assertIn(str(tree), resumed.stdout)
        self.assertEqual((tree / "tools/Fixture.csproj").read_text(), "tracked edit\n")
        self.assertEqual((tree / "untracked").read_text(), "untracked bytes\n")

    def test_make_explicit_reassignment_uses_stale_or_age_and_preserves_branch_refs(self):
        self.prepare_make()
        for reason, age in (("stale", -3600), ("age", 5 * 3600)):
            with self.subTest(reason=reason):
                tree = self.root / ("explicit " + reason)
                branch = "lane/governance/old-" + reason
                head = self.commit_branch(branch, tree, age)
                if reason == "stale":
                    self.make("worktree-return", cwd=tree)
                result = self.make("worktree", "KIND=governance", "NAME=new-" + reason,
                                   "DEST=" + str(tree), "BASE=" + self.base, "ALLOW_LOW_DISK=1", cwd=tree)
                self.assertIn('"status": "claimed"', result.stdout)
                self.assertEqual(run(tree, "branch", "--show-current").stdout.strip(),
                                 "lane/governance/new-" + reason)
                self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    def test_cli_cleans_later_expired_inventory_before_returning_claim_or_continuation(self):
        for continuation in (False, True):
            with self.subTest(continuation=continuation):
                eligible = self.root / ("a-eligible-" + str(continuation))
                expired = self.root / ("z-expired-" + str(continuation))
                name = "task-" + str(continuation)
                branch = "lane/governance/" + (name if continuation else "old-" + name)
                self.commit_branch(branch, eligible, 60 if continuation else 5 * 3600)
                old_branch = "lane/governance/expired-" + name
                head = self.commit_branch(old_branch, expired, 7 * 3600)
                (expired / "payload").write_text("dirty")
                (expired / "untracked").write_text("discard")
                result = self.create(name, self.root / "unused", reuse_any=True)
                self.assertFalse(expired.exists(), result.stdout)
                self.assertEqual(run(self.main, "rev-parse", old_branch).stdout.strip(), head)
                self.assertEqual(run(eligible, "branch", "--show-current").stdout.strip(),
                                 "lane/governance/" + name)
                # Keep the next subcase's inventory independent without a cleanup entrance.
                run(self.main, "worktree", "remove", "--force", eligible)

    def test_cli_expired_same_task_is_removed_and_reports_retained_branch_failure(self):
        tree = self.root / "expired same task"
        branch = "lane/governance/expired-task"
        head = self.commit_branch(branch, tree, 7 * 3600)
        (tree / "payload").write_text("ordinary tracked edit")
        (tree / "untracked").write_text("ordinary untracked bytes")
        failed = self.create("expired-task", tree, reuse_any=True, check=False, cwd=tree)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("branch_already_exists", failed.stderr)
        self.assertIn("expired_worktrees_removed=", failed.stderr)
        self.assertIn(str(tree), failed.stderr)
        self.assertNotIn("WORKTREE_RETAINED", failed.stderr)
        self.assertFalse(tree.exists())
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)

    def test_cli_same_task_still_checks_base_and_pins(self):
        tree = self.root / "same task"
        self.commit_branch("lane/governance/same", tree, 60)
        (tree / "lean-toolchain").write_text("incompatible pin\n")
        failed = self.create("same", self.root / "unused", reuse_any=True, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("incompatible_pin", failed.stderr)
        self.assertEqual((tree / "lean-toolchain").read_text(), "incompatible pin\n")
        (tree / "lean-toolchain").write_bytes((self.main / "lean-toolchain").read_bytes())
        (self.main / "new-base").write_text("different ancestry")
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "new base")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        failed = self.create("same", tree, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("incompatible_base", failed.stderr)

    def test_cli_continuation_retains_downstream_pin_validation(self):
        (self.main / "Reg/lakefile.toml").unlink()
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "invalid fixture pin")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        tree = self.root / "malformed pin"
        self.commit_branch("lane/governance/malformed", tree, 60)
        failed = self.create("malformed", self.root / "unused", reuse_any=True, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("REG-MANIFEST-INVALID", failed.stderr)
        self.assertTrue((tree / "payload").exists())

    def test_make_clean_all_expires_trees_even_when_artifact_mutex_is_held(self):
        self.prepare_make()
        tree = self.root / "expired"
        branch = "lane/governance/expired"
        head = self.commit_branch(branch, tree, 7 * 3600)
        (tree / "payload").write_text("discard tracked bytes")
        (tree / "untracked").write_text("discard untracked bytes")
        lock_path = self.root / "tmp" / ("trureturing-clean-all-" + str(os.getuid()) + ".lock")
        with lock_path.open("w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.make("-C", "tools", "clean-all", "FORCE=1", "BASE=" + self.base,
                               "CLEAN_TMP_ROOT=" + str(self.root / "artifacts"), check=False, cwd=tree)
        self.assertNotEqual(result.returncode, 0)  # Artifact owner retains its native refusal.
        self.assertIn("HOST_CLEANUP_FAILED", result.stderr)
        self.assertFalse(tree.exists(), result.stdout + result.stderr)
        self.assertEqual(run(self.main, "rev-parse", branch).stdout.strip(), head)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_explicit_cli_rejects_alias_foreign_and_main_without_reassignment(self):
        tree = self.root / "candidate"
        branch = "lane/governance/candidate"
        head = self.commit_branch(branch, tree, 5 * 3600)
        alias = self.root / "alias"
        alias.symlink_to(tree, target_is_directory=True)
        failed = self.create("new", alias, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("missing_or_linked_tree", failed.stderr)
        self.assertEqual(run(tree, "rev-parse", "HEAD").stdout.strip(), head)
        foreign = self.root / "foreign"
        run(self.root, "init", "--initial-branch=dev", foreign)
        failed = self.create("new", foreign, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("repository_identity", failed.stderr)
        failed = self.create("new", self.main, check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("main_worktree", failed.stderr)
        self.assertEqual(run(self.main, "branch", "--show-current").stdout.strip(), "dev")

    def test_expiry_native_failure_reports_partial_effects_before_selection(self):
        from worktree_protocol import GitFailure
        good = self.root / "a-expired"
        blocked = self.root / "z-expired"
        for name, path in (("good", good), ("blocked", blocked)):
            self.commit_branch("lane/governance/" + name, path, 7 * 3600)
        remove = pool._remove_registered
        def native_failure(source, path):
            if path.resolve() == blocked.resolve():
                raise GitFailure("native removal error")
            return remove(source, path)
        with patch.object(pool, "_remove_registered", side_effect=native_failure):
            with self.assertRaisesRegex(protocol.GitFailure, "expired_cleanup_failed:.*native removal error.*expired_worktrees_removed="):
                pool.claim(self.options("lane/governance/new"))
        self.assertFalse(good.exists())
        self.assertTrue(blocked.exists())
        self.assertNotEqual(run(self.main, "show-ref", "--verify", "refs/heads/lane/governance/new", check=False).returncode, 0)

    def test_pool_exact_six_hour_boundary_and_future_stale(self):
        tree = self.root / "boundary"
        self.commit_branch("lane/governance/boundary", tree, 6 * 3600)
        stamp = protocol.head_committer_time(tree)
        with patch.object(pool.time, "time", return_value=stamp + 6 * 3600):
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(result["items"][0]["outcome"], "retained")
        with patch.object(pool.time, "time", return_value=stamp + 6 * 3600 + 1):
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(result["items"][0]["outcome"], "removed")
        future = self.root / "future"
        self.commit_branch("lane/governance/future", future, -3600)
        self.assertFalse(protocol.reusable(future, self.main)[0])
        protocol.mark_stale(self.main, future)
        self.assertTrue(protocol.reusable(future, self.main)[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
