"""Actual embedded CLI and Make stdout, exit and reminder boundaries."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import agent_state_cases as cases


class AgentEntranceTests(unittest.TestCase):
    setUp = cases.AgentStateTests.setUp
    tearDown = cases.AgentStateTests.tearDown
    cli = cases.AgentStateTests.cli
    create = cases.AgentStateTests.create
    commit_branch = cases.AgentStateTests.commit_branch
    options = cases.AgentStateTests.options
    prepare_make = cases.AgentStateTests.prepare_make
    make = cases.AgentStateTests.make
    local = cases.AgentStateTests.local
    saved = cases.AgentStateTests.saved

    def test_observation_with_preserves_allocation_stdout_and_exit(self):
        tree = self.root / "wrapped"
        with cases.agent("codex:owner"):
            self.create("wrapped", tree)
        with cases.agent("claude:observer"):
            before = self.local(tree).read_bytes()
            result = self.cli("worktree", "with", "--path", tree, "--", sys.executable, "-c",
                              "print('child-only'); raise SystemExit(17)", check=False)
            self.assertEqual(result.returncode, 17)
            self.assertEqual(result.stdout, "child-only\n")
            self.assertEqual(result.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertIn('"pending": 0', result.stderr)
            self.assertEqual(self.local(tree).read_bytes(), before)
            pending = self.cli("worktree", "pending")
            self.assertEqual(json.loads(pending.stdout)["pending"], [])
            self.assertEqual(pending.stderr.count("WORKTREE_AGENT_PENDING "), 1)
        with cases.agent("codex:owner"):
            result = self.cli("worktree", "with", "--path", tree, "--", sys.executable, "-c", "pass")
            self.assertIn(str(tree), result.stderr)
            for guidance in ("maintain:", "worktree-checkpoint", "worktree-stale", "worktree-remove"):
                self.assertIn(guidance, result.stderr)

    def test_checkpoint_publication_failures_and_released_new_checkpoint(self):
        tree = self.root / "publication"
        with cases.agent("codex:publisher"):
            self.create("publication", tree)
            missing = self.cli("worktree", "checkpoint", "--path", tree, "--message-file", self.root / "missing",
                               check=False)
            self.assertEqual(missing.returncode, 73)
            self.assertEqual(missing.stdout, "")
            self.assertEqual(missing.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            published = self.cli("worktree", "publish", "--path", tree, "--branch", "wrong", check=False)
            self.assertEqual(published.returncode, 73)
            self.assertIn("publication_branch_mismatch", published.stderr)
            self.assertEqual(published.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            released = self.cli("worktree", "return", "--path", tree)
            self.assertEqual(json.loads(released.stdout)["status"], "stale")
            self.assertIn('"pending": 0', released.stderr)
            (tree / "new-source").write_text("ordinary source\n")
            message = self.root / "message"
            message.write_text("Checkpoint source\n")
            result = self.cli("worktree", "checkpoint", "--path", tree, "--message-file", message)
            self.assertEqual(json.loads(result.stdout)["status"], "committed")
            self.assertEqual(result.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertIn('"pending": 1', result.stderr)
            self.assertEqual(cases.run(tree, "status", "--porcelain").stdout, "")

    def test_make_create_claim_pending_cleanup_and_named_removal(self):
        with cases.agent("codex:maker"):
            self.prepare_make()
        tree = self.root / "make-tree"
        created = self.make("worktree", "KIND=governance", "NAME=maker", "BASE=" + self.base,
                            "DEST=" + str(tree), "ALLOW_LOW_DISK=1")
        self.assertEqual(created.stderr.count("WORKTREE_AGENT_PENDING "), 1)
        self.assertEqual(self.saved(tree)["creator"], "codex:maker")
        self.env["WORKTREE_AGENT_ID"] = "claude:maker"
        resumed = self.make("worktree", "KIND=governance", "NAME=maker", "BASE=" + self.base,
                            "DEST=" + str(tree), "ALLOW_LOW_DISK=1")
        self.assertEqual(resumed.stderr.count("WORKTREE_AGENT_PENDING "), 1)
        self.assertEqual(self.saved(tree)["allocation"]["agent"], "claude:maker")
        view = self.make("-s", "worktree-pending")
        self.assertEqual(json.loads(view.stdout)["pending"][0]["matched_by"], ["allocation"])
        self.assertEqual(view.stderr.count("WORKTREE_AGENT_PENDING "), 1)
        for force in ([], ["FORCE=1"]):
            cleaned = self.make("-C", "tools", "clean-lanes", *force)
            self.assertEqual(cleaned.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertIn('"pending": 1', cleaned.stderr)
            self.assertTrue(tree.is_dir())
        removed = self.make("worktree-remove", "NAMES=" + tree.name)
        self.assertEqual(removed.stderr.count("WORKTREE_AGENT_PENDING "), 1)
        self.assertIn("WORKTREE_REMOVE_RESULT exit=0 removed=1", removed.stdout)
        self.assertIn('"pending": 0', removed.stderr)
        refused = self.make("worktree-remove", "NAMES=absent", check=False)
        self.assertEqual(refused.returncode, 2)
        self.assertIn("WORKTREE_REMOVE_RESULT exit=65", refused.stdout)
        self.assertEqual(refused.stderr.count("WORKTREE_AGENT_PENDING "), 1)

    def test_auxiliary_capture_and_summary_failure_preserve_successful_create_exit(self):
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        launcher = bin_dir / "python3"
        launcher.write_text('#!/bin/bash\nfor arg in "$@"; do\n'
            ' if [[ "$arg" == record-registration || "$arg" == pending ]]; then\n'
            '  echo auxiliary-injected-failure >&2; exit 29\n fi\ndone\n'
            'exec "$STATE_TEST_PYTHON" "$@"\n')
        launcher.chmod(0o755)
        tree = self.root / "unattributed"
        with cases.agent("codex:one"):
            result = self.cli("worktree", "--kind", "governance", "--name", "unattributed", "--path", tree,
                "--base", self.base, "--skip-restore", env={"PATH": str(bin_dir) + os.pathsep + os.environ["PATH"],
                "STATE_TEST_PYTHON": sys.executable})
            self.assertEqual(result.returncode, 0)
            self.assertEqual(json.loads(result.stdout)["status"], "succeeded")
            self.assertIn("attribution unavailable", result.stderr)
            self.assertIn("pending summary unavailable", result.stderr)
            self.assertIn("auxiliary-injected-failure", result.stderr)
            self.assertFalse(self.local(tree).exists())

    def test_creation_summary_uses_source_clone_despite_ambient_git_directory(self):
        tree = self.root / "scoped"
        with cases.agent("codex:scoped"):
            result = self.cli("worktree", "--kind", "governance", "--name", "scoped", "--path", tree,
                "--base", self.base, "--skip-restore", env={"GIT_DIR": str(self.root / "remote.git")})
            self.assertEqual(json.loads(result.stdout)["status"], "succeeded")
            self.assertEqual(self.saved(tree)["creator"], "codex:scoped")
            self.assertIn('"pending": 1', result.stderr)
            self.assertIn(str(tree), result.stderr)
            self.assertEqual(result.stderr.count("WORKTREE_AGENT_PENDING "), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
