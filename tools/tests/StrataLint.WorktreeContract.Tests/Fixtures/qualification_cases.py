"""Batched qualification retains independent refusal and operational outcomes."""

from contextlib import redirect_stdout
import io
import json
import subprocess
from unittest.mock import patch


class QualificationCases:
    def batch_qualification_preserves_each_reason_and_tree(self):
        import worktree_protocol as protocol
        recent = self.root / "recent"
        self.g(self.main, "worktree", "add", "-b", "lane/governance/recent", recent, "HEAD")
        self.g(self.main, "worktree", "lock", "--reason", "manual", recent)
        self.g(self.main, "worktree", "lock", "--reason", "worktree-init:malformed", self.tree)
        result = self.run_protocol("qualify", "--path", recent, "--path", self.tree)
        items = {item["path"]: item for item in json.loads(result.stdout)["items"]}
        self.assertEqual("locked_recent", items[str(recent)]["reason"])
        self.assertEqual("refused", items[str(recent)]["outcome"])
        self.assertEqual("qualified", items[str(self.tree)]["outcome"])
        self.assertEqual("", result.stderr)
        self.assertTrue(recent.is_dir())
        self.assertTrue(self.tree.is_dir())
        self.assertIn("locked", protocol.identity(self.main, recent)[0])
        self.assertIn("locked", protocol.identity(self.main, self.tree)[0])

        with patch.object(protocol, "git", wraps=protocol.git) as calls, redirect_stdout(io.StringIO()):
            self.assertEqual(0, protocol.main(["--source", str(self.main), "qualify",
                                             "--path", str(recent), "--path", str(self.tree)]))
        inventories = [call for call in calls.call_args_list
                       if call.args[1:3] == ("worktree", "list")]
        self.assertEqual(1, len(inventories))

    def batch_qualification_reports_errors_without_hiding_other_results(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        paths = [self.root / name for name in ("timeout", "git", "os", "unexpected", "refused")]
        failures = [subprocess.TimeoutExpired(["git"], 300, stderr=b"native deadline"),
                    protocol.GitFailure("fatal: qualification git failed"),
                    OSError("qualification file unavailable"), RuntimeError("unexpected error"),
                    protocol.Refused("initialization_in_progress")]
        output = io.StringIO()
        with patch.object(preservation, "qualify", side_effect=failures), redirect_stdout(output):
            arguments = ["--source", str(self.main), "qualify"]
            for path in paths:
                arguments.extend(["--path", str(path)])
            self.assertEqual(74, protocol.main(arguments))
        result = json.loads(output.getvalue())
        self.assertEqual("failed", result["status"])
        items = result["items"]
        self.assertEqual(["failed"] * 4 + ["refused"], [item["outcome"] for item in items])
        self.assertIn("qualification_failed:timeout:", items[0]["reason"])
        self.assertIn("native deadline", items[0]["reason"])
        self.assertIn("GitFailure:fatal: qualification git failed", items[1]["reason"])
        self.assertIn("OSError:qualification file unavailable", items[2]["reason"])
        self.assertIn("RuntimeError:unexpected error", items[3]["reason"])
        self.assertEqual("initialization_in_progress", items[4]["reason"])

    def qualification_process_boundary_distinguishes_operational_errors(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        from contextlib import redirect_stderr
        for action in ("qualify", "preview", "preflight", "scoped"):
            for error in (protocol.GitFailure("fatal: native qualification broke"),
                          OSError("qualification filesystem broke"),
                          subprocess.TimeoutExpired(["git"], 300, stderr=b"inner deadline"),
                          protocol.Refused("initialization_in_progress")):
                with self.subTest(action=action, error=type(error).__name__):
                    original = preservation.qualify
                    calls = []
                    def injected(*args, **kwargs):
                        calls.append(True)
                        if len(calls) == (2 if action == "scoped" else 1):
                            raise error
                        return original(*args, **kwargs)
                    args = ["--source", str(self.main), "qualify" if action == "qualify" else "remove",
                            "--path", str(self.tree)]
                    if action == "preview":
                        args.append("--preview")
                    output, errors = io.StringIO(), io.StringIO()
                    with patch.object(preservation, "qualify", side_effect=injected), redirect_stdout(output), redirect_stderr(errors):
                        code = protocol.main(args)
                    refused = type(error) is protocol.Refused
                    self.assertEqual((0 if action == "qualify" else 73) if refused else 74, code)
                    self.assertTrue(self.tree.is_dir())
                    text = output.getvalue() + errors.getvalue()
                    self.assertIn("initialization_in_progress" if refused else "qualification_failed:", text)
                    if not refused:
                        self.assertIn("inner deadline" if isinstance(error, subprocess.TimeoutExpired) else str(error), text)

    def qualification_stream_preserves_completed_and_defers_unreached(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        refused, slow, unreached = [self.root / name for name in ("refused", "slow", "unreached")]
        def injected(source, path, **kwargs):
            if path == refused:
                raise protocol.Refused("locked_recent")
            if path == slow:
                import time
                time.sleep(1)
            self.fail("unreached tree was qualified")
        output = io.StringIO()
        snapshot, common = preservation.inventory(self.main), preservation.common(self.main)
        with patch.object(preservation, "inventory", return_value=snapshot), patch.object(preservation, "common", return_value=common), patch.object(preservation, "qualify", side_effect=injected), redirect_stdout(output):
            code = protocol.main(["--source", str(self.main), "qualify", "--stream", "--budget-seconds", "0.02",
                                  "--path", str(refused), "--path", str(slow), "--path", str(unreached)])
        self.assertEqual(74, code)
        rows = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(["refused", "failed", "deferred"], [row["outcome"] for row in rows[:-1]])
        self.assertEqual("locked_recent", rows[0]["reason"])
        self.assertIn("deadline", rows[1]["reason"])
        self.assertIn("deadline", rows[2]["reason"])
        self.assertEqual("failed", rows[-1]["status"])

    def pool_removal_qualification_preserves_refusal_and_operational_failure(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        import worktree_pool as pool
        self.pool_return()
        original = preservation.qualify
        for force in (False, True):
            for stage in ((1, 2) if force else (1,)):
                for refused in (False, True):
                    with self.subTest(force=force, stage=stage, refused=refused):
                        calls = []
                        def injected(*args, **kwargs):
                            calls.append(True)
                            if len(calls) == stage:
                                raise (protocol.Refused("initialization_in_progress") if refused
                                       else protocol.GitFailure("fatal: pool qualification broke"))
                            return original(*args, **kwargs)
                        with patch.object(pool, "available_fraction", return_value=0.04), patch.object(preservation, "qualify", side_effect=injected):
                            result = pool.sweep(self.main, self.base, force=force)
                        self.assertTrue(self.tree.is_dir())
                        row = result["items"][0]
                        self.assertEqual("succeeded" if refused else "failed", result["status"])
                        if refused:
                            self.assertEqual("retained", row["outcome"])
                            self.assertEqual("initialization_in_progress", row["reason"])
                        else:
                            self.assertIn("pool qualification broke", json.dumps(row))
