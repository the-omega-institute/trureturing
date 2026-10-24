"""Return, bounded idle retention and allocation probes using real Git."""

from contextlib import ExitStack
import json
import os
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch


class IdlePoolCases:
    def pool_github(self, **changes):
        payload = dict(state="MERGED", baseRefName="dev", headRefName=self.branch,
                       headRefOid=self.base, mergeCommit=dict(oid=self.base), autoMergeRequest=None)
        payload.update(changes)
        stub = self.root / "github-bin"
        stub.mkdir(exist_ok=True)
        data = self.root / "github.json"
        data.write_text(json.dumps(payload))
        gh = stub / "gh"
        gh.write_text("#!" + sys.executable + "\nfrom pathlib import Path\nprint(Path(" + repr(str(data)) + ").read_text())\n")
        gh.chmod(0o755)
        self.pool_env = dict(os.environ, PATH=str(stub) + os.pathsep + os.environ["PATH"])

    def pool_return(self, expect=0, joined=True):
        self.pool_github() if not hasattr(self, "pool_env") else None
        return self.run_protocol("return", "--path", self.tree, "--pr", "42",
                                 *(["--writers-joined"] if joined else []), expect=expect, env=self.pool_env)

    def pool_claim(self, branch="lane/math/next", path=None, base=None, expect=0):
        args = ["claim", "--skip-restore", "--branch", branch, "--base", base or self.base]
        if path is not None:
            args += ["--path", path]
        return self.run_protocol(*args, expect=expect)

    def test_pool_return_preserves_post_merge_work_branch_and_cache(self):
        self.pool_github()
        cache = self.tree / ".lake"
        cache.mkdir()
        exclude = self.root / "ignore"
        exclude.write_text(".lake/\n")
        self.g(self.main, "config", "core.excludesFile", exclude)
        (self.tree / ".gitignore").write_text(".lake/\n")
        (cache / "sentinel").write_text("cache bytes")
        (self.tree / "owned").write_text("after merge\n")
        result = json.loads(self.pool_return().stdout)
        self.assertEqual("returned", result["status"])
        saved = self.g(self.main, "show", self.branch + ":owned")
        self.assertEqual("after merge\n", saved)
        self.assertEqual(1, len(result["commits_not_in_dev"]))
        self.assertTrue(self.g(self.tree, "branch", "--show-current").strip().startswith("lane/governance/idle-"))
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        self.assertEqual("cache bytes", (cache / "sentinel").read_text())
        self.assertEqual("already_idle", json.loads(self.pool_return().stdout)["status"])

    def test_pool_return_requires_join_and_real_merge_evidence(self):
        self.assertIn("host_must_join", self.pool_return(expect=73, joined=False).stderr)
        for changes, reason in [
            (dict(state="CLOSED"), "pr_closed_not_merged"),
            (dict(state="OPEN"), "pr_open_not_merged"),
            (dict(state="OPEN", autoMergeRequest={"enabledAt":"now"}), "pr_auto_merge_pending"),
            (dict(baseRefName="other"), "pr_base_mismatch"),
            (dict(headRefName="other"), "pr_head_mismatch"),
            (dict(mergeCommit=None), "pr_merge_commit_missing")]:
            with self.subTest(changes=changes):
                self.pool_github(**changes)
                self.assertIn(reason, self.pool_return(expect=73).stderr)
                self.assertEqual(self.branch, self.g(self.tree, "branch", "--show-current").strip())

    def test_pool_return_refuses_unretained_merge_wrong_head_and_busy_writer(self):
        (self.tree / "owned").write_text("task\n")
        self.g(self.tree, "commit", "-am", "task")
        task = self.g(self.tree, "rev-parse", "HEAD").strip()
        self.pool_github(mergeCommit=dict(oid=task))
        self.assertIn("remote_does_not_retain_commit", self.pool_return(expect=73).stderr)
        self.pool_github(headRefOid=task)
        self.g(self.tree, "reset", "--hard", self.base)
        self.assertIn("pr_head_outside_tree", self.pool_return(expect=73).stderr)
        self.pool_github()
        job = self.hold()
        self.assertIn("busy_scope", self.pool_return(expect=73).stderr)
        job.stdin.write("done\n")
        job.stdin.flush()
        job.communicate(timeout=10)

    def test_pool_return_refuses_conflicts_operations_and_main(self):
        self.pool_github()
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        (metadata / "MERGE_HEAD").write_text(self.base + "\n")
        self.assertIn("unfinished_operation", self.pool_return(expect=73).stderr)
        (metadata / "MERGE_HEAD").unlink()
        result = self.run_protocol("return", "--path", self.main, "--pr", "42", "--writers-joined", expect=73, env=self.pool_env)
        self.assertIn("main_worktree", result.stderr)

    def test_pool_claim_writes_immutable_allocation_and_preserves_cache(self):
        self.pool_return()
        old = self.g(self.tree, "branch", "--show-current").strip()
        result = json.loads(self.pool_claim(path=self.tree).stdout)
        self.assertEqual("claimed", result["status"])
        self.assertEqual(str(self.tree), result["path"])
        self.assertEqual("lane/math/next", self.g(self.tree, "branch", "--show-current").strip())
        self.assertEqual("", self.g(self.main, "for-each-ref", "--format=%(refname)", "refs/heads/" + old))
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        fields, message = (metadata / "logs/HEAD").read_text().splitlines()[-1].split("\t")
        self.assertEqual([self.base, self.base], fields.split()[:2])
        self.assertEqual(result["allocation_time"], int(fields.rsplit(" ", 2)[1]))
        self.assertRegex(message, r"^worktree-allocation:[0-9a-f]{32}$")

    def test_pool_claim_requires_matching_pins_and_clean_idle_attachment(self):
        self.pool_return()
        (self.main / "lean-toolchain").write_text("other pins\n")
        self.g(self.main, "commit", "-am", "pins")
        other = self.g(self.main, "rev-parse", "HEAD").strip()
        self.assertEqual("no_idle", json.loads(self.pool_claim(base=other).stdout)["status"])
        self.assertIn("incompatible_pin", self.pool_claim(path=self.tree, base=other, expect=73).stderr)
        (self.tree / "owned").write_text("new work\n")
        self.assertIn("idle_dirty", self.pool_claim(path=self.tree, expect=73).stderr)
        self.g(self.tree, "reset", "--hard", self.base)
        self.g(self.tree, "switch", "--detach", self.base)
        self.assertEqual("no_idle", json.loads(self.pool_claim().stdout)["status"])

    def test_pool_claim_concurrency_has_one_winner(self):
        self.pool_return()
        commands = [[sys.executable, "-B", str(self.source_root / "tools/scripts/worktree/worktree_protocol.py"),
                     "--source", str(self.main), "claim", "--path", str(self.tree), "--base", self.base,
                     "--skip-restore", "--branch", "lane/math/contender-" + str(i)] for i in range(2)]
        jobs = [subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for cmd in commands]
        self.jobs.extend(jobs)
        results = [(job.communicate(timeout=30), job.returncode) for job in jobs]
        self.assertEqual(1, sum(code == 0 for _, code in results), results)
        self.assertTrue(all(code in (0, 73) for _, code in results), results)

    def test_pool_capacity_and_pressure_use_one_owner(self):
        import worktree_pool as pool
        idle = []
        for i in range(5):
            target = self.tree if i == 0 else self.root / ("idle-" + str(i))
            if i:
                self.g(self.main, "worktree", "add", "-b", "lane/governance/extra-" + str(i), target, self.base)
            self.g(target, "switch", "-c", "lane/governance/idle-" + str(i), self.base)
            idle.append(target)
        with patch.object(pool, "available_fraction", return_value=1):
            result = pool.sweep(self.main, self.base, force=False)
            self.assertEqual(1, sum(row["outcome"] == "would_remove" for row in result["items"]))
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(1, sum(row["outcome"] == "removed" for row in result["items"]))
        with patch.object(pool, "available_fraction", return_value=0.04):
            result = pool.sweep(self.main, self.base, force=True)
            self.assertEqual(4, sum(row["outcome"] == "removed" for row in result["items"]))
        self.assertFalse(any(target.exists() for target in idle))
