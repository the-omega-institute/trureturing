"""Detached snapshot recovery through native Git failures and retries."""

import argparse
from contextlib import ExitStack
import json
from pathlib import Path
from unittest.mock import patch
import uuid


class DetachedRecoveryCases:
    def test_clean_detached_recovery(self):
        self.detached_recovery(dirty=False)

    def test_dirty_detached_recovery(self):
        self.detached_recovery(dirty=True)

    def detached_recovery(self, dirty):
        self.g(self.tree, "checkout", "--detach")
        self.g(self.tree, "commit", "--allow-empty", "-m", "detached history")
        head = self.g(self.tree, "rev-parse", "HEAD").strip()
        self.g(self.main, "remote", "remove", "origin")
        if dirty:
            (self.tree / "owned").write_text("staged bytes\n")
            self.g(self.tree, "add", "owned")
            (self.tree / "owned").write_text("final tracked\n")
            (self.tree / "other").unlink()
            (self.tree / "untracked").write_text("final untracked\n")
            (self.main / ".git/info/exclude").write_text("ignored-output\n")
            (self.tree / "ignored-output").write_text("not required\n")
        result = json.loads(self.remove().stdout)["items"][0]
        reference = result["recovery_branch"]
        self.assertTrue(reference.startswith("refs/heads/lane/governance/recovery-"))
        self.assertFalse(self.tree.exists())
        self.assertEqual("committed" if dirty else "unchanged", result["checkpoint"]["status"])
        self.assertEqual(head, result["checkpoint"]["parent"])
        self.assertEqual(self.base, self.g(self.main, "rev-parse", self.branch).strip())
        self.g(self.main, "worktree", "add", self.tree, reference.removeprefix("refs/heads/"))
        self.assertEqual("final tracked\n" if dirty else "original\n", (self.tree / "owned").read_text())
        if dirty:
            self.assertEqual(head, self.g(self.tree, "rev-parse", "HEAD^").strip())
            self.assertEqual("final untracked\n", (self.tree / "untracked").read_text())
            self.assertFalse((self.tree / "other").exists())
            self.assertFalse((self.tree / "ignored-output").exists())
        else:
            self.assertEqual(head, self.g(self.tree, "rev-parse", "HEAD").strip())

    def test_detached_commit_failures_retry(self):
        self.g(self.tree, "checkout", "--detach")
        (self.tree / "owned").write_text("retry snapshot\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        for blocker in (metadata / "index.lock", self.main / ".git/hooks/pre-commit"):
            blocker.write_text("#!/bin/sh\nexit 1\n")
            blocker.chmod(0o755)
            result = json.loads(self.remove(74).stdout)["items"][0]
            self.assertEqual("checkpoint_failed", result["outcome"])
            self.assertIsNone(result["recovery_branch"])
            self.assertTrue(self.tree.exists())
            self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
            self.assertEqual("retry snapshot\n", (self.tree / "owned").read_text())
            blocker.unlink()
        result = json.loads(self.remove().stdout)["items"][0]
        self.g(self.main, "worktree", "add", self.tree, result["recovery_branch"].removeprefix("refs/heads/"))
        self.assertEqual("retry snapshot\n", (self.tree / "owned").read_text())

    def test_detached_branch_failures_and_collision_retry(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        for failure in ("collision", "native_lock", "scope", "after_create"):
            with self.subTest(failure=failure):
                self.g(self.tree, "checkout", "--detach")
                (self.tree / "owned").write_text(failure + " snapshot\n")
                token = uuid.uuid4()
                branch = "lane/governance/recovery-" + token.hex
                reference = "refs/heads/" + branch
                lock = self.main / (".git/" + reference + ".lock")
                if failure == "collision":
                    self.g(self.main, "branch", branch, self.base)
                if failure == "native_lock":
                    lock.parent.mkdir(parents=True, exist_ok=True)
                    lock.write_text("native ref writer\n")
                with ExitStack() as stack:
                    if failure == "scope":
                        protocol.acquire(stack, self.main, "ref:" + reference, True)
                    if failure == "after_create":
                        native_git = preservation.git
                        def fail_after_create(root, *args, **kwargs):
                            result = native_git(root, *args, **kwargs)
                            if args[:2] == ("branch", "--"):
                                raise protocol.GitFailure("failure after native branch creation")
                            return result
                        stack.enter_context(patch.object(preservation, "git", side_effect=fail_after_create))
                    with patch.object(preservation.uuid, "uuid4", return_value=token):
                        result = preservation.remove(options)["items"][0]
                self.assertEqual("checkpoint_failed", result["outcome"])
                self.assertIsNone(result["recovery_branch"])
                self.assertEqual(reference, result["recovery_branch_candidate"])
                head = self.g(self.tree, "rev-parse", "HEAD").strip()
                self.assertEqual(head, result["checkpoint"]["commit"])
                self.assertEqual(failure + " snapshot\n", self.g(self.tree, "show", "HEAD:owned"))
                self.assertEqual("", self.g(self.tree, "branch", "--show-current").strip())
                if failure == "collision":
                    self.assertEqual(self.base, self.g(self.main, "rev-parse", reference).strip())
                if failure == "after_create":
                    self.assertEqual(head, self.g(self.main, "rev-parse", reference).strip())
                if failure == "native_lock":
                    lock.unlink()
                retried = json.loads(self.remove().stdout)["items"][0]
                self.assertEqual("unchanged", retried["checkpoint"]["status"])
                self.assertEqual(head, retried["checkpoint"]["commit"])
                self.g(self.main, "worktree", "add", self.tree,
                       retried["recovery_branch"].removeprefix("refs/heads/"))
                self.assertEqual(failure + " snapshot\n", (self.tree / "owned").read_text())

    def test_detached_native_removal_partial_effect_keeps_recovery(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        self.g(self.tree, "checkout", "--detach")
        (self.tree / "owned").write_text("removed but recoverable\n")
        native_git = preservation.git
        def fail_after_remove(root, *args, **kwargs):
            if args[:2] == ("worktree", "remove"):
                reference = protocol.value(self.main, "for-each-ref", "--format=%(refname)",
                                           "refs/heads/lane/governance/recovery-*")
                self.assertTrue(reference)
                with ExitStack() as contender, self.assertRaises(protocol.Refused):
                    protocol.acquire(contender, self.main, "ref:" + reference, True)
                with ExitStack() as contender, self.assertRaises(protocol.Refused):
                    protocol.git_scope(contender, self.main, self.tree)
            result = native_git(root, *args, **kwargs)
            if args[:2] == ("worktree", "remove"):
                raise protocol.GitFailure("failure after native removal")
            return result
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        with patch.object(preservation, "git", side_effect=fail_after_remove):
            result = preservation.remove(options)["items"][0]
        self.assertEqual("partial_or_indeterminate", result["outcome"])
        self.assertFalse(self.tree.exists())
        self.g(self.main, "worktree", "add", self.tree, result["recovery_branch"].removeprefix("refs/heads/"))
        self.assertEqual("removed but recoverable\n", (self.tree / "owned").read_text())

    def test_detached_interrupted_removal_resumes_with_recorded_recovery(self):
        self.g(self.tree, "checkout", "--detach")
        (self.tree / "owned").write_text("detached before removal\n")
        reference = self.interrupted_removal()["recovery_branch"]
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual(("removed", reference), (result["outcome"], result["recovery_branch"]))
        self.assertEqual(reference, self.g(self.main, "for-each-ref", "--format=%(refname)",
                                           "refs/heads/lane/governance/recovery-*").strip())
        self.assertEqual("detached before removal\n", self.g(self.main, "show", reference + ":owned"))

    def test_detached_unfinished_and_unmerged_retained_before_staging(self):
        import worktree_protocol as protocol
        self.g(self.tree, "checkout", "--detach")
        (self.tree / "owned").write_text("unfinished snapshot\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        for name in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer"):
            marker = metadata / name
            if name.endswith("HEAD"):
                marker.write_text(self.base + "\n")
            else:
                marker.mkdir()
            result = self.remove(74)
            self.assertIn("unfinished_operation:" + name, result.stdout)
            self.assertEqual("", self.g(self.tree, "diff", "--cached", "--name-only"))
            marker.unlink() if marker.is_file() else marker.rmdir()
        oid = self.g(self.tree, "rev-parse", "HEAD:owned").strip()
        protocol.git(self.tree, "update-index", "--index-info",
                     input=f"0 {'0' * len(oid)}\towned\n100644 {oid} 1\towned\n100644 {oid} 2\towned\n".encode())
        self.assertIn("unmerged_index", self.remove(74).stdout)
        self.assertTrue(self.g(self.tree, "ls-files", "--unmerged"))
        self.assertEqual("", self.g(self.main, "for-each-ref", "--format=%(refname)", "refs/heads/lane/governance/recovery-*"))
        self.g(self.tree, "add", "owned")
        result = json.loads(self.remove().stdout)["items"][0]
        self.g(self.main, "worktree", "add", self.tree, result["recovery_branch"].removeprefix("refs/heads/"))
        self.assertEqual("unfinished snapshot\n", (self.tree / "owned").read_text())

    def interrupted_ignore_snapshot(self):
        (self.tree / ".gitignore").write_text("/cache/\n*.tmp\n")
        (self.tree / "nested").mkdir()
        (self.tree / "nested/.gitignore").write_text("!keep.tmp\noutput/\n")
        self.g(self.tree, "add", ".gitignore", "nested/.gitignore")
        self.g(self.tree, "commit", "-m", "snapshot ignore rules")
        (self.tree / "cache").mkdir()
        (self.tree / "cache/generated").write_text("ignored output\n")
        (self.tree / "nested/strange\nname.tmp").write_text("nested ignored output\n")
        (self.tree / "nested/output").mkdir()
        (self.tree / "nested/output/generated").write_text("nested rule output\n")
        snapshot = self.interrupted_removal()["checkpoint"]["commit"]
        for name in (".gitignore", "nested/.gitignore"):
            (self.tree / name).unlink()
        return snapshot

    def test_interrupted_removal_uses_snapshot_ignore_rules(self):
        snapshot = self.interrupted_ignore_snapshot()
        self.assertIn("?? cache/generated", self.g(self.tree, "status", "--porcelain", "--untracked-files=all"))
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual(("removed", "resumed"), (result["outcome"], result["checkpoint"]["status"]))
        self.assertFalse(self.tree.exists())
        self.assertEqual(snapshot, self.g(self.main, "rev-parse", self.branch).strip())
        self.assertEqual("/cache/\n*.tmp\n", self.g(self.main, "show", self.branch + ":.gitignore"))

    def test_interrupted_ignore_loss_preserves_later_changes(self):
        snapshot = self.interrupted_ignore_snapshot()
        for name, stage in (("later", False), ("nested/keep.tmp", False),
                            ("dir/child", False), ("staged", True)):
            with self.subTest(path=name, staged=stage):
                path = self.tree / name
                previous = path.read_bytes() if path.exists() else None
                path.write_text("later bytes\n")
                if stage:
                    self.g(self.tree, "add", name)
                result = json.loads(self.remove(74).stdout)["items"][0]
                self.assertIn("interrupted_removal_tree_changed", result["error"])
                self.assertEqual("later bytes\n", path.read_text())
                self.assertEqual(snapshot, self.g(self.main, "rev-parse", self.branch).strip())
                if stage:
                    self.g(self.tree, "reset", "--", name)
                if previous is None:
                    path.unlink()
                else:
                    path.write_bytes(previous)
        self.assertTrue(self.tree.exists())

    def test_interrupted_ignore_loss_keeps_snapshot_identity_guard(self):
        self.interrupted_ignore_snapshot()
        self.g(self.tree, "commit", "--allow-empty", "-m", "later history")
        result = json.loads(self.remove(74).stdout)["items"][0]
        self.assertIn("interrupted_removal_snapshot_moved", result["error"])
        self.assertTrue((self.tree / "cache/generated").is_file())
