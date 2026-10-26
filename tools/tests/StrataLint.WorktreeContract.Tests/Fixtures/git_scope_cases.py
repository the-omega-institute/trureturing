"""Git scope identity failures retain native state at consumer boundaries."""

from contextlib import contextmanager, ExitStack, redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import subprocess
from unittest.mock import patch


class GitScopeCases:
    @contextmanager
    def symbolic_ref_failure(self, returncode=128, stderr=b"fatal: symbolic HEAD read failed\n"):
        import worktree_protocol as protocol
        native = protocol.git

        def injected(root, *args, **kwargs):
            if Path(root) == self.tree and args == ("symbolic-ref", "--quiet", "HEAD"):
                return subprocess.CompletedProcess(args, returncode, b"", stderr)
            return native(root, *args, **kwargs)

        with patch.object(protocol, "git", side_effect=injected) as calls:
            yield calls

    def git_scope_rejects_operational_symbolic_ref_errors(self):
        import worktree_protocol as protocol
        for returncode, stderr in ((2, b"fatal: symbolic HEAD read failed\n"),
                                   (128, b"fatal: symbolic HEAD read failed\n"),
                                   (-15, b"fatal: symbolic HEAD read failed\n"),
                                   (128, b"")):
            with self.subTest(returncode=returncode, stderr=stderr), \
                    self.symbolic_ref_failure(returncode, stderr), ExitStack() as stack:
                with self.assertRaises(protocol.GitFailure) as failure:
                    protocol.git_scope(stack, self.main, self.tree)
                self.assertEqual(stderr.decode().strip() or "git failed", str(failure.exception))

    def git_scope_symbolic_ref_failure_retains_removal(self):
        import worktree_protocol as protocol
        (self.tree / "owned").write_text("staged snapshot\n")
        self.g(self.tree, "add", "owned")
        (self.tree / "owned").write_text("ordinary snapshot\n")
        metadata = Path(self.g(self.tree, "rev-parse", "--absolute-git-dir").strip())
        index = (metadata / "index").read_bytes()
        head_log = (metadata / "logs/HEAD").read_bytes()
        output = io.StringIO()
        with self.symbolic_ref_failure(), redirect_stdout(output):
            code = protocol.main(["--source", str(self.main), "remove", "--path", str(self.tree)])
        self.assertEqual(74, code, output.getvalue())
        result = json.loads(output.getvalue())
        self.assertEqual("failed", result["status"])
        row = result["items"][0]
        self.assertEqual("checkpoint_failed", row["outcome"])
        self.assertIn("symbolic HEAD read failed", row["error"])
        self.assertIsNone(row["checkpoint"])
        self.assertIsNone(row["recovery_branch"])
        self.assertEqual(index, (metadata / "index").read_bytes())
        self.assertEqual(head_log, (metadata / "logs/HEAD").read_bytes())
        self.assertEqual("ordinary snapshot\n", (self.tree / "owned").read_text())
        self.assertEqual(self.branch, self.g(self.tree, "branch", "--show-current").strip())
        self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
        self.assertFalse(self.g(self.main, "for-each-ref", "refs/heads/lane/governance/recovery-*").strip())

    def git_scope_symbolic_ref_failure_fails_pool_inspection(self):
        import worktree_pool as pool
        import worktree_protocol as protocol
        self.make_idle(self.tree, self.base)
        reference = self.g(self.tree, "symbolic-ref", "HEAD").strip()
        for force in (False, True):
            with self.subTest(force=force):
                output = io.StringIO()
                with self.symbolic_ref_failure(), patch.object(pool, "available_fraction", return_value=0.04), \
                        redirect_stdout(output):
                    code = protocol.main(["--source", str(self.main), "pool", "--dev", self.base]
                                         + (["--force"] if force else []))
                self.assertEqual(74, code, output.getvalue())
                result = json.loads(output.getvalue())
                self.assertEqual("failed", result["status"])
                row = result["items"][0]
                self.assertEqual("sweep_failed", row["outcome"])
                self.assertEqual("inspect", row["stage"])
                self.assertEqual("GitFailure", row["error_type"])
                self.assertIn("symbolic HEAD read failed", row["error"])
                self.assertTrue(self.tree.is_dir())
                self.assertEqual(reference, self.g(self.tree, "symbolic-ref", "HEAD").strip())

    def git_scope_symbolic_ref_failure_stops_pool_claim(self):
        import worktree_protocol as protocol
        self.make_idle(self.tree, self.base)
        reference = self.g(self.tree, "symbolic-ref", "HEAD").strip()
        branch = "lane/governance/claim-failed-symbolic-head"
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                output, errors = io.StringIO(), io.StringIO()
                with self.symbolic_ref_failure(), redirect_stdout(output), redirect_stderr(errors):
                    code = protocol.main(["--source", str(self.main), "claim", "--branch", branch,
                                          "--base", self.base, "--skip-restore"]
                                         + (["--path", str(self.tree)] if explicit else []))
                self.assertEqual(73, code, output.getvalue() + errors.getvalue())
                self.assertEqual("", output.getvalue())
                self.assertIn("symbolic HEAD read failed", errors.getvalue())
                self.assertTrue(self.tree.is_dir())
                self.assertEqual(reference, self.g(self.tree, "symbolic-ref", "HEAD").strip())
                self.assertFalse(self.g(self.main, "for-each-ref", "refs/heads/" + branch).strip())

    def git_scope_symbolic_ref_failure_stops_pool_return(self):
        import worktree_protocol as protocol
        output, errors = io.StringIO(), io.StringIO()
        with self.symbolic_ref_failure(), redirect_stdout(output), redirect_stderr(errors):
            code = protocol.main(["--source", str(self.main), "return", "--path", str(self.tree),
                                  "--writers-joined"])
        self.assertEqual(73, code, output.getvalue() + errors.getvalue())
        self.assertEqual("", output.getvalue())
        self.assertIn("symbolic HEAD read failed", errors.getvalue())
        self.assertTrue(self.tree.is_dir())
        self.assertEqual(self.branch, self.g(self.tree, "branch", "--show-current").strip())
        self.assertFalse(self.g(self.main, "for-each-ref", "refs/heads/lane/governance/idle-*").strip())

    def git_scope_symbolic_ref_failure_stops_commands(self):
        import worktree_protocol as protocol
        (self.tree / "owned").write_text("uncommitted snapshot\n")
        commands = (["with", "--git", "--", "true"], ["checkpoint"],
                    ["publish", "--branch", self.branch],
                    ["reuse", "--branch", self.branch, "--base", self.base])
        for command in commands:
            with self.subTest(command=command):
                output, errors = io.StringIO(), io.StringIO()
                with self.symbolic_ref_failure(), patch.object(protocol.os, "execvpe") as execute, \
                        redirect_stdout(output), redirect_stderr(errors):
                    code = protocol.main(["--source", str(self.main), command[0], "--path", str(self.tree)]
                                         + command[1:])
                self.assertEqual(73, code, output.getvalue() + errors.getvalue())
                self.assertEqual("", output.getvalue())
                self.assertIn("symbolic HEAD read failed", errors.getvalue())
                execute.assert_not_called()
                self.assertEqual(self.base, self.g(self.tree, "rev-parse", "HEAD").strip())
                self.assertEqual("uncommitted snapshot\n", (self.tree / "owned").read_text())
