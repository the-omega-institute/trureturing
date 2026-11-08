"""Actual embedded CLI and Make stdout, exit and reminder boundaries."""
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import socket
import subprocess
import sys
import threading
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

    def test_with_reminder_reaches_caller_while_child_waits_for_release(self):
        tree = self.root / "waiting"
        child = ("import socket, sys; s = socket.socket(socket.AF_UNIX); "
                 "s.connect(sys.argv[1]); s.sendall(b'ready'); s.recv(1); "
                 "print('child-only'); print('child-error', file=sys.stderr); raise SystemExit(17)")
        with cases.agent("codex:waiting"):
            self.create("waiting", tree)
            entrances = {
                "direct": [sys.executable, "-B", str(cases.ROOT / "tools/scripts/worktree/worktree_protocol.py"),
                           "--source", str(self.main)],
                "embedded": [shutil.which("dotnet"), str(cases.ROOT /
                             "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"), "worktree"],
            }
            for entrance, command in entrances.items():
                with self.subTest(entrance=entrance), socket.socket(socket.AF_UNIX) as listener:
                    address = str(self.root / (entrance + ".sock"))
                    listener.bind(address)
                    listener.listen(1)
                    listener.settimeout(20)
                    errors, reminder = [], threading.Event()
                    process = subprocess.Popen(command + ["with", "--path", str(tree), "--",
                        sys.executable, "-c", child, address], cwd=self.main,
                        env=cases.protocol.git_environment(), text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, start_new_session=True)

                    def read_errors():
                        for line in process.stderr:
                            errors.append(line)
                            if line.startswith("WORKTREE_AGENT_PENDING "):
                                reminder.set()

                    reader = threading.Thread(target=read_errors)
                    reader.start()
                    try:
                        with listener.accept()[0] as connection:
                            connection.settimeout(20)
                            self.assertEqual(connection.recv(5), b"ready")
                            try:
                                self.assertTrue(reminder.wait(10),
                                    entrance + ": no reminder visible while child is active")
                                self.assertIsNone(process.poll())
                            finally:
                                connection.sendall(b"x")
                        process.wait(timeout=20)
                        reader.join(timeout=20)
                        self.assertFalse(reader.is_alive())
                        self.assertEqual(process.returncode, 17)
                        self.assertEqual(process.stdout.read(), "child-only\n")
                        error = "".join(errors)
                        self.assertEqual(error.count("WORKTREE_AGENT_PENDING "), 1)
                        self.assertIn('"pending": 1', error)
                        self.assertIn(str(tree), error)
                        self.assertEqual(error.count("child-error\n"), 1)
                        self.assertLess(error.index("WORKTREE_AGENT_PENDING "), error.index("child-error\n"))
                    finally:
                        if process.poll() is None:
                            os.killpg(process.pid, signal.SIGKILL)
                        process.wait(timeout=20)
                        reader.join(timeout=20)
                        process.stdout.close()
                        process.stderr.close()

    def check_explicit_source_summary(self, fail_checkout):
        invoking, tree = self.root / "invoking", self.root / "target-tree"
        cases.run(self.root, "clone", "--no-local", self.main, invoking)
        environment = {}
        if fail_checkout:
            bin_dir = self.root / "fail-bin"
            bin_dir.mkdir()
            launcher = bin_dir / "git"
            launcher.write_text('#!/bin/bash\nif [[ "$1" == reset ]]; then echo injected-early-checkout >&2; exit 42; fi\n'
                                'exec ' + shlex.quote(shutil.which("git")) + ' "$@"\n')
            launcher.chmod(0o755)
            environment["PATH"] = str(bin_dir) + os.pathsep + os.environ["PATH"]
        with cases.agent("codex:target"):
            result = self.cli("worktree", "--kind", "governance", "--name", "target", "--path", tree,
                "--source", "../main" if fail_checkout else self.main, "--base", self.base,
                "--skip-restore", cwd=invoking, check=False, env=environment)
            self.assertEqual(result.returncode, 2 if fail_checkout else 0, result.stdout + result.stderr)
            if fail_checkout:
                self.assertEqual(result.stdout, "")
                self.assertIn("injected-early-checkout", result.stderr)
                self.assertFalse((tree / "lean-toolchain").exists())
            else:
                self.assertEqual(json.loads(result.stdout)["status"], "succeeded")
            self.assertEqual(self.saved(tree)["creator"], "codex:target")
            self.assertEqual(result.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertIn('"complete": true', result.stderr)
            self.assertIn('"pending": 1', result.stderr)
            self.assertIn(str(tree), result.stderr)
            target = json.loads(self.cli("worktree", "pending").stdout)
            unrelated = json.loads(self.cli("worktree", "pending", cwd=invoking).stdout)
            self.assertEqual([row["path"] for row in target["pending"]], [str(tree)])
            self.assertTrue(unrelated["complete"])
            self.assertEqual(unrelated["pending"], [])

    def test_explicit_source_creation_summary_uses_target_clone(self):
        self.check_explicit_source_summary(fail_checkout=False)

    def test_explicit_source_retained_failure_summary_uses_target_clone(self):
        self.check_explicit_source_summary(fail_checkout=True)

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
