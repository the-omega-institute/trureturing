"""Disposable native Git attribution, failure and concurrency contracts."""
from contextlib import contextmanager, redirect_stderr
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import unittest
from unittest.mock import patch

import stale_lifecycle_cases as lifecycle
ROOT, run, pool, protocol = lifecycle.ROOT, lifecycle.run, lifecycle.pool, lifecycle.protocol
import worktree_agent_state as state
import worktree_publication as publication

IDENTITIES = ("WORKTREE_AGENT_ID", "CODEX_THREAD_ID", "CODEX_SESSION_ID", "CLAUDE_CODE_SESSION_ID")


@contextmanager
def agent(value=None, **values):
    env = {key: val for key, val in os.environ.items() if key not in IDENTITIES}
    if value is not None:
        env["WORKTREE_AGENT_ID"] = value
    with patch.dict(os.environ, env | values, clear=True):
        yield


class AgentStateTests(unittest.TestCase):
    # Reuse the lifecycle fixture's native repository and actual CLI/Make doors.
    setUp = lifecycle.LifecycleTests.setUp
    tearDown = lifecycle.LifecycleTests.tearDown
    cli = lifecycle.LifecycleTests.cli
    create = lifecycle.LifecycleTests.create
    commit_branch = lifecycle.LifecycleTests.commit_branch
    options = lifecycle.LifecycleTests.options
    prepare_make = lifecycle.LifecycleTests.prepare_make
    make = lifecycle.LifecycleTests.make

    def local(self, path):
        return protocol.identity(self.main, path)[1] / state.STATE

    def saved(self, path):
        return json.loads(self.local(path).read_text())

    def view(self):
        with redirect_stderr(io.StringIO()) as output:
            result = state.report(self.main)
        self.assertEqual(output.getvalue().count("WORKTREE_AGENT_PENDING "), 1)
        return result

    def test_exact_identity_precedence_no_fallback_and_environment_propagation(self):
        self.assertEqual(state.caller({}), (None, "identity_absent"))
        hosts = dict(WORKTREE_AGENT_ID="other:explicit", CODEX_THREAD_ID="thread",
                     CODEX_SESSION_ID="session", CLAUDE_CODE_SESSION_ID="claude")
        for name, expected in (("WORKTREE_AGENT_ID", "other:explicit"), ("CODEX_THREAD_ID", "codex:thread"),
                               ("CODEX_SESSION_ID", "codex:session"), ("CLAUDE_CODE_SESSION_ID", "claude:claude")):
            selected = {key: val for key, val in hosts.items() if IDENTITIES.index(key) >= IDENTITIES.index(name)}
            self.assertEqual(state.caller(selected)[0], expected)
        for bad in ("", "unscoped", "codex:has space", "codex:a:b", "codex:a\n", "Bad:case", "x:" + "a" * 161):
            self.assertEqual(state.caller({"WORKTREE_AGENT_ID": bad, "CODEX_THREAD_ID": "valid"})[0], None)
        for variable, expected in (("WORKTREE_AGENT_ID", "custom:host"), ("CODEX_THREAD_ID", "codex:host"),
                                    ("CODEX_SESSION_ID", "codex:host"), ("CLAUDE_CODE_SESSION_ID", "claude:host")):
            with agent(**{variable: "custom:host" if variable == "WORKTREE_AGENT_ID" else "host"}):
                path = self.root / variable.lower()
                result = self.create(variable.lower(), path)
                self.assertEqual(self.saved(path)["creator"], expected)
                self.assertEqual(result.stderr.count("WORKTREE_AGENT_PENDING "), 1)

    def test_two_agents_multiple_pending_release_new_commit_and_removal(self):
        with agent("codex:one"):
            first, second = self.root / "first", self.root / "second"
            self.create("first", first)
            self.create("second", second)
        with agent("claude:two"):
            other = self.root / "other"
            self.create("other", other)
            self.assertEqual([row["path"] for row in self.view()["pending"]], [str(other)])
        with agent("codex:one"):
            view = self.view()
            self.assertTrue(view["complete"])
            self.assertEqual({row["path"] for row in view["pending"]}, {str(first), str(second)})
            self.assertEqual(view["pending"][0]["matched_by"], ["creator", "allocation"])
            released = self.cli("worktree", "stale", "--path", first)
            self.assertEqual(released.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertEqual(len(self.view()["pending"]), 1)
            run(first, "commit", "--allow-empty", "-m", "fresh work")
            self.assertEqual(len(self.view()["pending"]), 2)
            removed = self.cli("worktree", "remove", "--names", second.name)
            self.assertIn("WORKTREE_REMOVE_RESULT exit=0", removed.stdout)
            self.assertEqual(removed.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertEqual(len(self.view()["pending"]), 1)

    def test_unknown_and_legacy_creators_stay_unknown_on_known_claim(self):
        unknown, legacy = self.root / "unknown", self.root / "legacy"
        with agent():
            created = self.create("unknown", unknown)
            self.assertIn('"identity_reason": "identity_absent"', created.stderr)
            self.assertFalse(self.view()["complete"])
            self.assertIsNone(self.saved(unknown)["creator"])
        self.commit_branch("lane/governance/legacy", legacy, 60)
        with agent("codex:claim"):
            self.create("unknown", unknown)
            self.create("legacy", legacy)
            for tree in (unknown, legacy):
                self.assertIsNone(self.saved(tree)["creator"])
                self.assertEqual(self.saved(tree)["allocation"]["agent"], "codex:claim")
            view = self.view()
            self.assertFalse(view["complete"])
            self.assertEqual(len(view["pending"]), 2)
            self.assertTrue(all(row["matched_by"] == ["allocation"] for row in view["pending"]))

    def test_same_task_cross_agent_claim_branch_drift_and_reregistration(self):
        tree = self.root / "shared"
        with agent("codex:creator"):
            self.create("shared", tree)
        with agent("claude:claimant"):
            self.create("shared", tree)
            self.assertEqual(self.saved(tree)["creator"], "codex:creator")
            self.assertEqual(self.view()["pending"][0]["matched_by"], ["allocation"])
            run(tree, "switch", "-c", "lane/governance/continued")
            self.assertEqual(self.view()["pending"], [])
            self.assertIsNone(self.saved(tree)["allocation"])
            run(tree, "switch", "lane/governance/shared")
            self.assertEqual(self.view()["pending"], [])
            self.create("shared", tree)
            self.assertEqual(len(self.view()["pending"]), 1)
        with agent():
            self.create("shared", tree)
            self.assertEqual(self.saved(tree)["allocation"]["agent"], "claude:claimant")
        with agent("codex:creator"):
            self.assertEqual(self.view()["pending"][0]["matched_by"], ["creator"])
            protocol.mark_stale(self.main, tree)
        with agent("claude:replacement"):
            result = self.create("replacement", tree)
            self.assertEqual(json.loads(result.stdout)["status"], "claimed")
            self.assertEqual(self.saved(tree)["creator"], "claude:replacement")
            self.assertEqual(self.saved(tree)["allocation"]["branch"], "refs/heads/lane/governance/replacement")
        with agent("codex:creator"):
            self.assertEqual(self.view()["pending"], [])

    def test_branch_switch_does_not_transfer_release_and_scan_failure_is_incomplete(self):
        tree = self.root / "switched"
        with agent("codex:one"):
            self.create("switched", tree)
            protocol.mark_stale(self.main, tree)
            self.assertEqual(self.view()["pending"], [])
            run(tree, "switch", "-c", "lane/governance/next-task")
            view = self.view()
            self.assertEqual(view["pending"][0]["reason"], "no_stale_marker")
            self.assertEqual(view["pending"][0]["matched_by"], ["creator"])
            with patch.object(protocol, "inventory", side_effect=TimeoutError("agent_state_budget_exhausted")):
                view = self.view()
            self.assertFalse(view["complete"])
            self.assertIn("agent_state_budget_exhausted", view["unknown"][0]["reason"])

    def test_capture_precedes_checkout_failure_then_explicit_recovery(self):
        tree = self.root / "early"
        real_git = __import__("shutil").which("git")
        bin_dir = self.root / "fail-bin"
        bin_dir.mkdir()
        launcher = bin_dir / "git"
        launcher.write_text('#!/bin/bash\nif [[ "$1" == reset ]]; then echo injected-early-checkout >&2; exit 42; fi\n'
                            'exec ' + __import__("shlex").quote(real_git) + ' "$@"\n')
        launcher.chmod(0o755)
        with agent("codex:early"):
            failed = self.cli("worktree", "--kind", "governance", "--name", "early", "--path", tree,
                              "--base", self.base, "--skip-restore", check=False,
                              env={"PATH": str(bin_dir) + os.pathsep + os.environ["PATH"]})
            self.assertEqual(failed.returncode, 2, failed.stdout + failed.stderr)
            self.assertIn("injected-early-checkout", failed.stderr)
            self.assertEqual(failed.stderr.count("WORKTREE_AGENT_PENDING "), 1)
            self.assertFalse((tree / "lean-toolchain").exists())
            self.assertEqual(self.saved(tree)["creator"], "codex:early")
        # Native recovery restores the checkout; canonical same-task setup then
        # validates branch/base/pins and explicitly claims it for the new caller.
        run(tree, "reset", "--hard", "HEAD")
        with agent("claude:recovery"):
            recovered = self.create("early", tree)
            self.assertEqual(json.loads(recovered.stdout)["status"], "reused")
            self.assertEqual(self.saved(tree)["creator"], "codex:early")
            self.assertEqual(self.saved(tree)["allocation"]["agent"], "claude:recovery")

    def test_pool_and_mirror_capture_before_failed_setup(self):
        tree = self.root / "pool"
        self.commit_branch("lane/governance/old", tree, 5 * 3600)
        original = protocol.git
        def fail_reset(root, *args, **kwargs):
            if args[:1] == ("reset",):
                raise protocol.GitFailure("injected-pool-checkout")
            return original(root, *args, **kwargs)
        with agent("codex:pool"), patch.object(pool, "git", side_effect=fail_reset):
            with self.assertRaisesRegex(protocol.GitFailure, "injected-pool-checkout"):
                pool.claim(self.options("lane/governance/pool", tree))
        self.assertEqual(self.saved(tree)["creator"], "codex:pool")
        mirror = self.root / "mirror"
        remote = self.root / "remote.git"
        run(self.main, "remote", "add", "origin", remote)
        options = self.options("lane/governance/mirror", mirror)
        options.remote, options.merge, options.message = "origin", self.base, "Mirror"
        with agent("claude:mirror"), patch.object(publication, "git", side_effect=fail_reset):
            with self.assertRaisesRegex(protocol.GitFailure, "injected-pool-checkout"):
                publication.prepare_mirror(options)
        self.assertEqual(self.saved(mirror)["creator"], "claude:mirror")
        hook = self.main / ".git/hooks/post-checkout"
        hook.write_text("#!/bin/sh\necho injected-mirror-hook >&2\nexit 43\n")
        hook.chmod(0o755)
        options.path, options.branch = self.root / "hook-mirror", "lane/governance/hook-mirror"
        with agent("claude:hook"):
            with self.assertRaisesRegex(protocol.GitFailure, "injected-mirror-hook"):
                publication.prepare_mirror(options)
        self.assertEqual(self.saved(options.path)["creator"], "claude:hook")
        self.assertTrue((options.path / "lean-toolchain").is_file())

    def test_malformed_unwritable_and_native_read_failure_are_advisory(self):
        tree = self.root / "damaged"
        with agent("codex:one"):
            self.create("damaged", tree)
            admin = self.local(tree).parent
            self.local(tree).write_text("{malformed")
            resumed = self.create("damaged", tree)
            self.assertEqual(resumed.returncode, 0)
            self.assertIn("WORKTREE_AGENT_WARNING", resumed.stderr)
            self.assertFalse(self.view()["complete"])
            self.assertEqual(self.local(tree).read_text(), "{malformed")
            self.local(tree).unlink()
            admin.chmod(0o500)
            try:
                resumed = self.create("damaged", tree)
                self.assertEqual(resumed.returncode, 0)
                self.assertIn("WORKTREE_AGENT_WARNING", resumed.stderr)
            finally:
                admin.chmod(0o700)
            state.record(self.main, tree, created=False)
            with patch.object(protocol, "stale_head", side_effect=protocol.GitFailure("marker_unreadable")):
                view = self.view()
            self.assertFalse(view["complete"])
            self.assertEqual(view["pending"][0]["status"], "unavailable")

    def test_nonblocking_concurrent_writers_preserve_creator_and_atomic_json(self):
        tree = self.root / "concurrent"
        with agent("codex:original"):
            self.create("concurrent", tree)
        branch = "lane/governance/concurrent"
        command = [sys.executable, "-B", str(ROOT / "tools/scripts/worktree/worktree_protocol.py"),
                   "--source", str(self.main), "reuse", "--path", str(tree), "--branch", branch, "--base", self.base]
        processes = [subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     env=protocol.git_environment({"WORKTREE_AGENT_ID": "codex:writer" + str(index)})) for index in range(5)]
        for process in processes:
            stdout, stderr = process.communicate(timeout=20)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertEqual(json.loads(stdout)["status"], "reused")
            self.assertEqual(stderr.count(b"WORKTREE_AGENT_PENDING "), 1)
            self.assertEqual(self.saved(tree)["creator"], "codex:original")
        self.assertFalse(list(self.local(tree).parent.glob(".agent-state-*")))
        fd = os.open(self.local(tree).parent, os.O_RDONLY)
        try:
            state.fcntl.flock(fd, state.fcntl.LOCK_EX | state.fcntl.LOCK_NB)
            result = subprocess.run(command, capture_output=True, env=protocol.git_environment(), timeout=20)
            self.assertEqual(result.returncode, 0)
            self.assertIn(b"WORKTREE_AGENT_WARNING", result.stderr)
        finally:
            os.close(fd)

    def test_delayed_writer_cannot_touch_recreated_registration(self):
        tree = self.root / "recreated"
        with agent("codex:old"):
            self.create("recreated", tree)
            entered, resume = threading.Event(), threading.Event()
            original = state.publish
            def paused(*args, **kwargs):
                entered.set()
                self.assertTrue(resume.wait(3))
                return original(*args, **kwargs)
            with patch.object(state, "publish", side_effect=paused):
                writer = threading.Thread(target=state.record, args=(self.main, tree))
                writer.start()
                self.assertTrue(entered.wait(3))
                run(self.main, "worktree", "remove", "--force", tree)
                self.assertFalse(tree.exists())
                run(self.main, "worktree", "add", tree, "lane/governance/recreated")
                # Keep replacement publication outside the paused writer.
                with state.registration(self.main, tree) as (fd, stamp, item, verify):
                    original(fd, dict(version=1, registration=stamp, creator="claude:new", allocation=None), verify)
                resume.set()
                writer.join(timeout=5)
                self.assertFalse(writer.is_alive())
            self.assertEqual(self.saved(tree)["creator"], "claude:new")
            self.assertIsNone(self.saved(tree)["allocation"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
