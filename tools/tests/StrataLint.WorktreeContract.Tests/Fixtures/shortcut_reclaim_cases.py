"""Shortcut reclaim checks under the acquired Git operation scope."""

import argparse
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import worktree_protocol as protocol
import worktree_preservation as preservation


class ShortcutReclaimCases:
    def shortcut_options(self):
        self.g(self.tree, "commit", "--allow-empty", "-m", "tree work")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        expected = dict(path=str(self.tree), head=self.g(self.tree, "rev-parse", "HEAD").strip(),
                        branch="refs/heads/" + self.branch, require_clean=True,
                        reflog_sha256=hashlib.sha256((metadata / "logs/HEAD").read_bytes().splitlines()[-1]).hexdigest())
        options = argparse.Namespace(source=self.main, path=[self.tree], names="", force=False,
                                     preview=False, expected=[json.dumps(expected)])
        return options, metadata, expected

    def assert_shortcut_scope_race_retained(self, change):
        options, metadata, expected = self.shortcut_options()
        original_scope = preservation.git_scope
        def changed_after_acquiring_scope(stack, source, target):
            branch = original_scope(stack, source, target)
            with ExitStack() as competitor:
                with self.assertRaisesRegex(protocol.Refused, "busy_scope"):
                    original_scope(competitor, source, target)
            if change == "reset":
                self.g(target, "reset", "--hard", "HEAD")
            elif change == "operation":
                (metadata / "MERGE_HEAD").write_text(expected["head"] + "\n")
            else:
                (target / "new-task").write_text("current task\n")
            return branch
        with patch.object(preservation, "git_scope", side_effect=changed_after_acquiring_scope):
            result = preservation.remove(options)
        self.assertEqual("failed", result["status"])
        item = result["items"][0]
        self.assertEqual("race_changed", item["error"])
        self.assertIsNone(item["checkpoint"])
        self.assertTrue(self.tree.exists())
        self.assertEqual(expected["head"], self.g(self.tree, "rev-parse", "HEAD").strip())
        if change == "dirty":
            self.assertEqual("current task\n", (self.tree / "new-task").read_text())

    def test_shortcut_reflog_rechecked_inside_git_scope(self):
        self.assert_shortcut_scope_race_retained("reset")

    def test_shortcut_dirty_rechecked_inside_git_scope(self):
        self.assert_shortcut_scope_race_retained("dirty")

    def test_shortcut_operation_rechecked_inside_git_scope(self):
        self.assert_shortcut_scope_race_retained("operation")

    def test_shortcut_only_last_reflog_record_is_expected(self):
        options, metadata, expected = self.shortcut_options()
        log = metadata / "logs/HEAD"
        lines = log.read_bytes().splitlines()
        lines[0] += b" older record annotation"
        log.write_bytes(b"\n".join(lines) + b"\n")
        result = preservation.remove(options)
        self.assertEqual("succeeded", result["status"])
        self.assertEqual(expected["head"], result["items"][0]["checkpoint"]["commit"])
        self.assertFalse(self.tree.exists())
