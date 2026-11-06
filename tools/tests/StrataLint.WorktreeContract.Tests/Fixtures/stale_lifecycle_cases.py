"""Disposable Git checks for the age/stale worktree lifecycle."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace

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
        self.root = Path(self.tmp.name)
        self.main = self.root / "main"
        run(self.root, "init", "--bare", self.root / "remote.git")
        run(self.root, "init", "--initial-branch=dev", self.main)
        run(self.main, "config", "user.name", "Lifecycle Tests")
        run(self.main, "config", "user.email", "lifecycle@example.invalid")
        (self.main / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (self.main / "lake-manifest.json").write_text('{"packages":[]}\n')
        run(self.main, "add", ".")
        run(self.main, "commit", "-m", "base")
        self.base = run(self.main, "rev-parse", "HEAD").stdout.strip()
        self.source = self.main

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
            result = pool.claim(self.options("lane/governance/reused"))
            self.assertEqual(result["status"], "claimed", result)
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
