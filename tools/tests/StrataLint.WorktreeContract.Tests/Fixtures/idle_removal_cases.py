"""Interrupted idle eviction and later-write boundaries using real Git."""

from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
from unittest.mock import patch


class IdleRemovalCases:
    def interrupted_idle(self, cache=False):
        import worktree_pool as pool
        import worktree_preservation as preservation
        (self.main / ".gitignore").write_text(".lake/\n")
        self.g(self.main, "add", ".gitignore")
        self.g(self.main, "commit", "-m", "Cache ignore")
        self.base = self.g(self.main, "rev-parse", "HEAD").strip()
        self.g(self.main, "push", "origin", "dev")
        self.g(self.tree, "reset", "--hard", self.base)
        self.make_idle(self.tree, self.base)
        if cache:
            (self.tree / ".lake").mkdir()
            (self.tree / ".lake/cache").write_bytes(b"rebuildable cache\n")

        def interrupt(target):
            (target / "owned").unlink()
            if cache:
                (target / ".gitignore").unlink()
            raise OSError("idle payload deletion interrupted")

        with patch.object(pool, "available_fraction", return_value=0.04), \
                patch.object(preservation, "remove_payload", side_effect=interrupt):
            result = pool.sweep(self.main, self.base, force=True)
        item, = result["items"]
        self.assertEqual(("failed", "partial_or_indeterminate"), (result["status"], item["outcome"]))
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        self.removal_record = metadata / preservation.REMOVAL_RECORD
        self.removal_bytes = self.removal_record.read_bytes()
        self.idle_branch = self.g(self.tree, "symbolic-ref", "HEAD").strip()
        record = json.loads(self.removal_bytes)
        self.assertEqual(self.base, record["commit"])
        self.assertEqual(self.idle_branch, record["recovery_branch"])
        self.assertEqual([], record.get("predecessors", []))
        expected = [" D .gitignore", " D owned", "?? .lake/cache"] if cache else [" D owned"]
        self.assertEqual(expected, self.g(self.tree, "status", "--porcelain", "--untracked-files=all").splitlines())

    def idle_removal_sweep(self, execute=False, expected=0):
        import worktree_pool as pool
        import worktree_protocol as protocol
        output = StringIO()
        with patch.object(pool, "available_fraction", return_value=1), redirect_stdout(output):
            code = protocol.main(["--source", str(self.main), "pool", "--dev", self.base,
                                  *(["--force"] if execute else [])])
        self.assertEqual(expected, code, output.getvalue())
        result = json.loads(output.getvalue())
        item, = result["items"]
        self.note("idle_removal_sweep", execute=execute, exit_code=code, item=item)
        return item

    def resume_idle_eviction(self, cache):
        import worktree_pool as pool
        self.interrupted_idle(cache=cache)
        item = self.idle_removal_sweep()
        self.assertEqual(("would_remove", "idle_interrupted_removal"), (item["outcome"], item["reason"]))
        self.assertTrue(self.tree.exists())
        self.assertEqual(self.removal_bytes, self.removal_record.read_bytes())
        with patch.object(pool, "remove", wraps=pool.remove) as common_remove:
            item = self.idle_removal_sweep(execute=True)
        self.assertEqual("removed", item["outcome"])
        self.assertEqual("resumed", item["checkpoint"]["status"])
        self.assertEqual(self.base, item["checkpoint"]["commit"])
        self.assertEqual(self.idle_branch, item["recovery_branch"])
        self.assertFalse(common_remove.call_args.args[0].force)
        self.assertFalse(self.tree.exists())
        self.assertNotIn("worktree " + str(self.tree) + "\n", self.g(self.main, "worktree", "list", "--porcelain"))
        self.assertEqual(self.base, self.g(self.main, "rev-parse", self.idle_branch).strip())
        self.assertEqual("original\n", self.g(self.main, "show", self.idle_branch + ":owned"))

    def pool_resumes_interrupted_eviction_without_cache(self):
        self.resume_idle_eviction(cache=False)

    def pool_resumes_interrupted_eviction_with_deleted_ignore(self):
        self.resume_idle_eviction(cache=True)

    def pool_pending_removal_does_not_displace_healthy_capacity(self):
        import worktree_pool as pool
        self.interrupted_idle()
        healthy = []
        for number in range(pool.IDLE_CAPACITY):
            target = self.root / ("healthy-" + str(number))
            self.g(self.main, "worktree", "add", "--detach", target, self.base)
            self.make_idle(target, self.base)
            healthy.append(target)
        with patch.object(pool, "available_fraction", return_value=1):
            result = pool.sweep(self.main, self.base, force=True)
        self.assertEqual("succeeded", result["status"])
        self.assertEqual([str(self.tree)], [row["path"] for row in result["items"] if row["outcome"] == "removed"])
        self.assertEqual(pool.IDLE_CAPACITY, sum(row["reason"] == "idle_pool" for row in result["items"]))
        self.assertTrue(all(target.exists() for target in healthy))

    def pool_retains_dirty_idle_without_removal_record(self):
        self.make_idle(self.tree, self.base)
        (self.tree / "owned").unlink()
        for execute in (False, True):
            item = self.idle_removal_sweep(execute=execute)
            self.assertEqual(("retained", "idle_dirty"), (item["outcome"], item["reason"]))
        self.assertTrue(self.tree.exists())
        self.assertIn("idle_dirty", self.pool_claim(path=self.tree, expect=73).stderr)

    def retain_later_idle_write(self, name):
        self.interrupted_idle()
        target = self.tree / name
        target.write_bytes(b"unique later content\n")
        for execute in (False, True):
            item = self.idle_removal_sweep(execute=execute)
            self.assertEqual(("retained", "interrupted_removal_tree_changed"),
                             (item["outcome"], item["reason"]))
            self.assertEqual(b"unique later content\n", target.read_bytes())
            self.assertEqual(self.removal_bytes, self.removal_record.read_bytes())
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())

    def pool_retains_interrupted_eviction_with_modified_file(self):
        self.retain_later_idle_write("other")

    def pool_retains_interrupted_eviction_with_untracked_file(self):
        self.retain_later_idle_write("later-ordinary")

    def pool_never_claims_pending_removal_even_when_clean(self):
        self.interrupted_idle()
        for clean in (False, True):
            with self.subTest(clean=clean):
                if clean:
                    self.g(self.tree, "restore", "owned")
                self.assertEqual("no_idle", json.loads(self.pool_claim().stdout)["status"])
                self.assertIn("idle_removal_pending", self.pool_claim(path=self.tree, expect=73).stderr)
                self.assertEqual(self.idle_branch, self.g(self.tree, "symbolic-ref", "HEAD").strip())
                self.assertEqual(self.removal_bytes, self.removal_record.read_bytes())
        self.assertEqual("would_remove", self.idle_removal_sweep()["outcome"])

    def pool_retains_mismatched_removal_record_without_reconverging(self):
        import worktree_preservation as preservation
        self.interrupted_idle()
        older = self.g(self.main, "rev-parse", "HEAD^").strip()
        for mismatch in ("commit", "recovery_branch"):
            with self.subTest(mismatch=mismatch):
                record = json.loads(self.removal_bytes)
                if mismatch == "commit":
                    record["commit"] = older
                else:
                    record["recovery_branch"] = "refs/heads/lane/governance/old-recovery"
                    self.g(self.main, "update-ref", record["recovery_branch"], older)
                self.removal_record.write_text(json.dumps(record))
                before = self.removal_record.read_bytes()
                refs = self.g(self.main, "show-ref")
                for execute in (False, True):
                    item = self.idle_removal_sweep(execute=execute)
                    self.assertEqual(("retained", "interrupted_removal_identity_changed"),
                                     (item["outcome"], item["reason"]))
                    self.assertEqual(before, self.removal_record.read_bytes())
                    self.assertEqual(refs, self.g(self.main, "show-ref"))
                    self.assertTrue(self.tree.exists())
        result = preservation.remove(self.removal_options())["items"][0]
        self.assertEqual(("removed", "reconverged"), (result["outcome"], result["checkpoint"]["status"]))
        self.assertIn(self.base, [self.g(self.main, "rev-parse", root).strip()
                                 for root in result["recovery_roots"]])
        self.assertEqual("original\n", self.g(self.main, "show", self.base + ":owned"))

    def pool_revalidates_interrupted_eviction_before_common_removal(self):
        import worktree_pool as pool
        self.interrupted_idle()
        def later_write(source):
            (self.tree / "late").write_bytes(b"unique concurrent content\n")
            return 1
        with patch.object(pool, "available_fraction", side_effect=later_write):
            result = pool.sweep(self.main, self.base, force=True)
        self.assertEqual("failed", result["status"])
        item, = result["items"]
        self.assertEqual(("retained", "interrupted_removal_tree_changed", "revalidate"),
                         (item["outcome"], item["reason"], item["stage"]))
        self.assertEqual(b"unique concurrent content\n", (self.tree / "late").read_bytes())
        self.assertEqual(self.removal_bytes, self.removal_record.read_bytes())

    def pool_pending_removal_keeps_unfinished_operation_guard(self):
        self.interrupted_idle()
        (self.removal_record.parent / "MERGE_HEAD").write_text(self.base + "\n")
        for execute in (False, True):
            item = self.idle_removal_sweep(execute=execute)
            self.assertEqual(("retained", "unfinished_operation:MERGE_HEAD"),
                             (item["outcome"], item["reason"]))
            self.assertEqual(self.removal_bytes, self.removal_record.read_bytes())
