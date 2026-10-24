"""Native lock, initialization and removal recovery behavior with real Git objects."""

import argparse
from contextlib import ExitStack
import json
from pathlib import Path
from unittest.mock import patch


class LockRecoveryCases:
    def test_holderless_native_locks_checkpoint_once(self):
        import worktree_protocol as protocol
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        for lock in (metadata / "index.lock", self.main / (".git/refs/heads/" + self.branch + ".lock")):
            with self.subTest(lock=str(lock)):
                lock.parent.mkdir(parents=True, exist_ok=True)
                lock.write_text("residual\n")
                (self.tree / "owned").write_text(str(lock) + "\n")
                result = self.checkpoint()
                self.assertIn("native_lock_cleared", result.stdout)
                self.assertFalse(lock.exists())
                self.assertEqual(str(lock) + "\n", self.g(self.tree, "show", "HEAD:owned"))
        with ExitStack() as stack:
            protocol.tree_scope(stack, self.main, self.tree, True)

    def test_held_native_lock_retains_exact_blocker(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        with lock.open("w") as holder:
            holder.write("live\n")
            holder.flush()
            result = self.checkpoint(expect=73)
            self.assertIn("native_lock_held:" + str(lock), result.stderr)
            self.assertTrue(lock.exists())

    def test_unverifiable_and_replaced_native_lock_retained(self):
        import worktree_protocol as protocol
        import worktree_publication as publication
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        options = argparse.Namespace(source=self.main, path=self.tree, message_file=None)
        lock.write_text("residual\n")
        with patch.object(protocol, "native_lock_holders", side_effect=OSError("inspection denied")):
            with self.assertRaisesRegex(protocol.Refused, "native_lock_unverifiable:"):
                publication.checkpoint(options)
        def replaced(path):
            replacement = path.with_name("replacement")
            replacement.write_text("replacement bytes\n")
            replacement.replace(path)
            return []
        with patch.object(protocol, "native_lock_holders", side_effect=replaced):
            with self.assertRaisesRegex(protocol.Refused, "native_lock_changed:"):
                publication.checkpoint(options)
        self.assertEqual("replacement bytes\n", lock.read_text())

    def test_native_clearance_requires_exclusive_tree(self):
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        lock = metadata / "index.lock"
        lock.write_text("residual\n")
        self.hold()
        self.checkpoint(expect=73)
        self.assertTrue(lock.exists())

    def test_dead_initializer_is_removable_without_lock_age(self):
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:dead", self.tree)
        self.remove()
        self.assertFalse(self.tree.exists())

    def test_live_initializer_is_retained(self):
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:alive", self.tree)
        self.hold("--exclusive")
        result = self.remove(expect=73)
        self.assertIn("initialization_in_progress", result.stderr)
        self.assertTrue(self.tree.exists())

    def owned_initialization(self, registered=True):
        import worktree_protocol as protocol
        token = "worktree-init:" + "a" * 32
        branch = "lane/governance/owned-init"
        target = self.root / "initializing"
        self.g(self.main, "update-ref", "--create-reflog", "-m", token,
               "refs/heads/" + branch, self.base, "0" * len(self.base))
        if registered:
            self.g(self.main, "worktree", "add", "--no-checkout", "--lock", "--reason", token, target, branch)
        return target, branch, token

    def test_failed_initialization_recovers_in_place_idempotently(self):
        target, branch, token = self.owned_initialization()
        (target / "owned").write_text("bytes from interrupted checkout\n")
        for attempt in range(2):
            self.run_protocol("recover-init", "--path", target, "--branch", branch,
                              "--base", self.base, "--skip-restore")
            self.assertEqual("bytes from interrupted checkout\n", (target / "owned").read_text())
            self.assertTrue((target / "other").is_file())
        references = self.g(self.main, "for-each-ref", "--format=%(refname)",
                            "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertTrue(references)
        self.assertTrue(any(self.g(self.main, "show", ref + ":owned") ==
                            "bytes from interrupted checkout\n" for ref in references))

    def test_owned_unregistered_branch_can_resume(self):
        target, branch, token = self.owned_initialization(registered=False)
        self.run_protocol("recover-init", "--path", target, "--branch", branch,
                          "--base", self.base, "--skip-restore")
        self.assertEqual("original\n", (target / "owned").read_text())

    def test_initialization_identity_changes_refuse_recovery(self):
        target, branch, token = self.owned_initialization()
        metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
        for failure in ("token", "branch", "backlink"):
            with self.subTest(failure=failure):
                saved = (metadata / "gitdir").read_text()
                if failure == "token":
                    (metadata / "locked").write_text("worktree-init:foreign\n")
                elif failure == "branch":
                    self.g(target, "symbolic-ref", "HEAD", "refs/heads/" + self.branch)
                else:
                    (metadata / "gitdir").write_text(str(self.tree / ".git") + "\n")
                self.run_protocol("recover-init", "--path", target, "--branch", branch,
                                  "--base", self.base, "--skip-restore", expect=73)
                (metadata / "locked").write_text(token + "\n")
                (metadata / "gitdir").write_text(saved)
                self.g(target, "symbolic-ref", "HEAD", "refs/heads/" + branch)
        self.assertFalse((target / "owned").exists())

    def test_removal_record_mismatch_reconverges_and_keeps_both_roots(self):
        original = self.interrupted_removal()["checkpoint"]["commit"]
        self.g(self.tree, "commit", "--allow-empty", "-m", "later head")
        (self.tree / "owned").write_text("current bytes\n")
        result = json.loads(self.remove().stdout)["items"][0]
        self.assertEqual("reconverged", result["checkpoint"]["status"])
        self.assertEqual("current bytes\n", self.g(self.main, "show", result["recovery_branch"] + ":owned"))
        refs = self.g(self.main, "for-each-ref", "--format=%(objectname)",
                      "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertIn(original, refs)

    def test_reconvergence_interruption_retains_record_and_recovery_objects(self):
        import worktree_preservation as preservation
        original = self.interrupted_removal()["checkpoint"]["commit"]
        self.g(self.tree, "commit", "--allow-empty", "-m", "moved snapshot")
        (self.tree / "owned").write_text("new bytes\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        options = argparse.Namespace(source=self.main, names="tree", path=[], force=False,
                                     preview=False, expected=[])
        with patch.object(preservation, "record_removal", side_effect=OSError("record interrupted")):
            result = preservation.remove(options)
        self.assertEqual("failed", result["status"])
        self.assertEqual(original, json.loads((metadata / "worktree-removal").read_text())["commit"])
        refs = self.g(self.main, "for-each-ref", "--format=%(objectname)",
                      "refs/heads/lane/governance/recovery-*").splitlines()
        self.assertIn(original, refs)
        self.assertIn(self.g(self.tree, "rev-parse", "HEAD").strip(), refs)
        self.remove()
