"""Batched qualification retains independent refusal and operational outcomes."""

from contextlib import redirect_stdout
import io
import json
import subprocess
from unittest.mock import patch


class QualificationCases:
    def qualification_intentional_lock_metadata_races(self):
        import os
        import worktree_protocol as protocol
        import worktree_publication as publication
        from contextlib import redirect_stderr
        from pathlib import Path
        self.g(self.main, "worktree", "lock", "--reason", "intentional", self.tree)
        lock = protocol.identity(self.main, self.tree)[1] / "locked"
        original_bytes = lock.read_bytes()
        old = 1000000000
        original_stat = Path.stat
        for action in ("qualify", "preview", "preflight", "scoped"):
            for change in ("unlock", "replace", "timestamp", "replace_error", "present_error", "present_missing_error"):
                with self.subTest(action=action, change=change):
                    os.utime(lock, (old, old))
                    backup = lock.with_name("prior-lock")
                    calls = []
                    threshold = 4 if action == "scoped" else 2
                    def injected(path, *args, **kwargs):
                        if (path == lock or path == str(lock)) and kwargs.get("follow_symlinks", True):
                            calls.append(True)
                            if len(calls) == threshold:
                                if change == "unlock":
                                    lock.unlink()
                                    raise FileNotFoundError("intentional lock metadata cause")
                                if change.startswith("replace"):
                                    lock.rename(backup)
                                    lock.write_bytes(original_bytes)
                                    os.utime(lock, (old, old))
                                if change == "timestamp":
                                    os.utime(lock, (old + 1, old + 1))
                                if change in ("replace_error", "present_error"):
                                    raise PermissionError("intentional lock metadata cause")
                                if change == "present_missing_error":
                                    raise FileNotFoundError("intentional lock metadata cause")
                        return original_stat(path, *args, **kwargs)
                    args = ["--source", str(self.main), "qualify" if action == "qualify" else "remove",
                            "--path", str(self.tree)]
                    if action == "preview":
                        args.append("--preview")
                    output, errors = io.StringIO(), io.StringIO()
                    try:
                        with patch.object(Path, "stat", new=injected), \
                                patch.object(publication, "commit_snapshot", side_effect=AssertionError("unexpected checkpoint")) as checkpoint, \
                                redirect_stdout(output), redirect_stderr(errors):
                            code = protocol.main(args)
                        self.assertGreaterEqual(len(calls), threshold)
                        self.assertTrue(self.tree.is_dir())
                        refused = not change.startswith("present")
                        self.assertEqual((0 if action == "qualify" else 73) if refused else 74, code)
                        text = output.getvalue() + errors.getvalue()
                        if refused:
                            self.assertIn("observed_identity_changed", text)
                            self.assertNotIn("qualification_failed:", text)
                        else:
                            self.assertIn("qualification_failed:", text)
                            self.assertIn("intentional lock metadata cause", text)
                        checkpoint.assert_not_called()
                    finally:
                        if backup.exists():
                            backup.replace(lock)
                        else:
                            lock.write_bytes(original_bytes)

    def pool_revalidation_keeps_refusal_and_prior_eviction(self):
        import worktree_protocol as protocol
        import worktree_pool as pool
        from pathlib import Path
        original = pool.qualify
        for change in ("disappeared", "identity", "refused", "native"):
            with self.subTest(change=change):
                older, newer = self.pool_pair(suffix=change)
                calls = []
                def injected(source, path, *args, **kwargs):
                    if Path(path) == newer:
                        calls.append(True)
                        if len(calls) == 2:
                            self.assertFalse(older.exists())
                            if change == "disappeared":
                                self.g(self.main, "worktree", "remove", newer)
                            elif change == "identity":
                                self.make_idle(newer, self.base)
                            elif change == "refused":
                                raise protocol.Refused("initialization_in_progress")
                            else:
                                raise protocol.GitFailure("fatal: revalidation native cause")
                    return original(source, path, *args, **kwargs)
                output = io.StringIO()
                with patch.object(pool, "qualify", side_effect=injected), \
                        patch.object(pool, "available_fraction", return_value=0.04), redirect_stdout(output):
                    code = protocol.main(["--source", str(self.main), "pool", "--dev", self.base, "--force"])
                self.assertEqual(2, len(calls))
                self.assertEqual(74, code)
                result = json.loads(output.getvalue().splitlines()[-1])
                self.assertEqual("failed", result["status"])
                removed = next(row for row in result["items"] if row["path"] == str(older))
                retained = next(row for row in result["items"] if row["path"] == str(newer))
                self.assertEqual("removed", removed["outcome"])
                self.assertEqual(self.base, removed["checkpoint"]["commit"])
                self.assertEqual(str(newer), retained["path"])
                self.assertEqual("revalidate", retained.get("stage"))
                self.assertTrue(retained.get("error"))
                if change == "native":
                    self.assertEqual("sweep_failed", retained["outcome"])
                    self.assertIn("revalidation native cause", retained["error"])
                else:
                    self.assertEqual("retained", retained["outcome"])
                    self.assertEqual(dict(disappeared="missing_or_linked_tree", identity="idle_identity_changed",
                                          refused="initialization_in_progress")[change], retained["reason"])
                self.assertEqual(change != "disappeared", newer.exists())
                if newer.exists():
                    self.g(self.main, "worktree", "remove", newer)

    def native_identity_races_are_refused(self):
        import worktree_protocol as protocol
        from pathlib import Path
        for native in ("--git-common-dir", "--show-toplevel", "--absolute-git-dir"):
            for change in ("tree", "marker", "identity", "pointer_format", "present"):
                with self.subTest(native=native, change=change):
                    marker, backup = self.tree / ".git", self.root / "disappeared"
                    original_marker, original_value = marker.read_bytes(), protocol.value
                    injected = []
                    def read(root, *args):
                        if Path(root).resolve() == self.tree.resolve() and native in args and not injected:
                            injected.append(True)
                            if change == "tree":
                                self.tree.rename(backup)
                            elif change == "marker":
                                marker.unlink()
                            elif change == "identity":
                                marker.write_text("gitdir: " + str(self.main / ".git") + "\n")
                            elif change == "pointer_format":
                                marker.write_bytes(original_marker.rstrip(b"\n"))
                            raise protocol.GitFailure("fatal: direct identity cause")
                        return original_value(root, *args)
                    try:
                        with patch.object(protocol, "value", side_effect=read), self.assertRaises(protocol.Refused) as caught:
                            protocol.identity(self.main, self.tree)
                        self.assertTrue(injected)
                        operational = change in ("present", "pointer_format")
                        self.assertIs(type(caught.exception), protocol.GitFailure if operational else protocol.Refused)
                        self.assertEqual("fatal: direct identity cause" if operational else dict(
                            tree="missing_or_linked_tree", marker="git_pointer", identity="git_pointer_identity")[change],
                            str(caught.exception))
                    finally:
                        if backup.exists():
                            backup.rename(self.tree)
                        marker.write_bytes(original_marker)

    def qualification_native_identity_races_are_refused(self):
        import worktree_protocol as protocol
        from contextlib import redirect_stderr
        from pathlib import Path
        for action in ("qualify", "preview", "preflight", "scoped"):
            for native in ("--git-common-dir", "--show-toplevel", "--absolute-git-dir"):
                for change in ("tree", "marker", "identity", "pointer_format", "present"):
                    with self.subTest(action=action, native=native, change=change):
                        marker = self.tree / ".git"
                        original_marker = marker.read_bytes()
                        backup = self.root / "disappeared"
                        original_value, calls = protocol.value, []
                        def injected(root, *args):
                            if Path(root).resolve() == self.tree.resolve() and native in args:
                                calls.append(True)
                                if len(calls) == (2 if action == "scoped" else 1):
                                    if change == "tree":
                                        self.tree.rename(backup)
                                    elif change == "marker":
                                        marker.unlink()
                                    elif change == "identity":
                                        marker.write_text("gitdir: " + str(self.main / ".git") + "\n")
                                    elif change == "pointer_format":
                                        marker.write_bytes(original_marker.rstrip(b"\n"))
                                    raise protocol.GitFailure("fatal: native identity race cause")
                            return original_value(root, *args)
                        args = ["--source", str(self.main), "qualify" if action == "qualify" else "remove",
                                "--path", str(self.tree)]
                        if action == "preview":
                            args.append("--preview")
                        output, errors = io.StringIO(), io.StringIO()
                        try:
                            with patch.object(protocol, "value", side_effect=injected), redirect_stdout(output), redirect_stderr(errors):
                                code = protocol.main(args)
                            self.assertTrue(calls)
                            text = output.getvalue() + errors.getvalue()
                            if change in ("present", "pointer_format"):
                                self.assertEqual(74, code)
                                self.assertIn("qualification_failed:", text)
                                self.assertIn("native identity race cause", text)
                            else:
                                self.assertEqual(0 if action == "qualify" else 73, code)
                                self.assertNotIn("qualification_failed:", text)
                                self.assertIn(dict(tree="missing_or_linked_tree", marker="git_pointer",
                                                   identity="git_pointer_identity")[change], text)
                        finally:
                            if backup.exists():
                                backup.rename(self.tree)
                            marker.write_bytes(original_marker)

    def pool_scope_operational_failure_is_failed(self):
        import worktree_protocol as protocol
        import worktree_pool as pool
        for error in (protocol.Refused("busy_scope:operation:idle-pool"),
                      protocol.GitFailure("fatal: pool entry qualification broke"), OSError("pool entry unavailable")):
            output = io.StringIO()
            with patch.object(pool, "acquire", side_effect=error), redirect_stdout(output):
                code = protocol.main(["--source", str(self.main), "pool", "--dev", self.base])
            self.assertEqual(74, code)
            result = json.loads(output.getvalue())
            self.assertEqual("failed", result["status"])
            self.assertEqual("refused" if type(error) is protocol.Refused else "failed", result["failure"]["outcome"])
            self.assertEqual(str(error), result["failure"]["error"])
            self.assertEqual([], result["items"])

    def pool_claim_qualification_failure_cannot_become_no_idle(self):
        import worktree_protocol as protocol
        import worktree_pool as pool
        from contextlib import redirect_stderr
        self.pool_return()
        for failed in (False, True):
            output, errors = io.StringIO(), io.StringIO()
            error = (protocol.GitFailure("fatal: claim qualification broke") if failed
                     else protocol.Refused("idle_locked"))
            with patch.object(pool, "qualify", side_effect=error), redirect_stdout(output), redirect_stderr(errors):
                code = protocol.main(["--source", str(self.main), "claim", "--branch",
                                      "lane/governance/qualification-claim", "--base", self.base, "--skip-restore"])
            self.assertEqual(73 if failed else 0, code)
            if failed:
                self.assertEqual("", output.getvalue())
                self.assertIn("fatal: claim qualification broke", errors.getvalue())
            else:
                self.assertEqual("no_idle", json.loads(output.getvalue())["status"])
            self.assertTrue(self.tree.is_dir())
            self.assertIn("lane/governance/idle-", self.g(self.tree, "branch", "--show-current"))
            self.assertFalse(self.g(self.main, "for-each-ref", "refs/heads/lane/governance/qualification-claim").strip())

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
        starts = [row["path"] for row in rows if row["event"] == "worktree_qualification_started"]
        self.assertEqual(list(map(str, (refused, slow))), starts)
        items = [row for row in rows if row["event"] == "worktree_qualification_item"]
        self.assertEqual(["refused", "failed", "deferred"], [row["outcome"] for row in items])
        self.assertEqual("locked_recent", items[0]["reason"])
        self.assertIn("deadline", items[1]["reason"])
        self.assertIn("deadline", items[2]["reason"])
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
                        output = io.StringIO()
                        with patch.object(pool, "available_fraction", return_value=0.04), \
                                patch.object(preservation, "qualify", side_effect=injected), redirect_stdout(output):
                            code = protocol.main(["--source", str(self.main), "pool", "--dev", self.base,
                                                  *(["--force"] if force else [])])
                        result = json.loads(output.getvalue())
                        self.assertTrue(self.tree.is_dir())
                        row = result["items"][0]
                        self.assertEqual(74, code)
                        self.assertEqual("failed", result["status"])
                        if refused:
                            self.assertEqual("retained", row["outcome"])
                            self.assertEqual("initialization_in_progress", row["reason"])
                            self.assertEqual(str(self.tree), row["path"])
                            self.assertEqual("remove", row["stage"])
                            self.assertEqual("initialization_in_progress", row["error"])
                        else:
                            self.assertIn("pool qualification broke", json.dumps(row))

    def pool_return_selected_eviction_refusal_fails_public_exit(self):
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        import worktree_pool as pool
        output = io.StringIO()
        with patch.object(pool, "available_fraction", return_value=0.04), \
                patch.object(preservation, "qualify", side_effect=protocol.Refused("locked_recent")), \
                redirect_stdout(output):
            code = protocol.main(["--source", str(self.main), "return", "--path", str(self.tree),
                                  "--writers-joined"])
        result = json.loads(output.getvalue())
        self.assertEqual("returned", result["status"])
        self.assertEqual(74, code)
        self.assertEqual("failed", result["pool"]["status"])
        row = next(row for row in result["pool"]["items"] if row["path"] == str(self.tree))
        self.assertEqual("retained", row["outcome"])
        self.assertEqual("locked_recent", row["reason"])
        self.assertEqual("remove", row["stage"])
        self.assertEqual("locked_recent", row["error"])
        self.assertTrue(self.tree.is_dir())

    def pool_final_qualification_defers_later_candidates(self):
        self.pool_final_qualification_failure_cases("pool")

    def pool_return_final_qualification_defers_later_candidates(self):
        self.pool_final_qualification_failure_cases("return")

    def pool_final_qualification_failure_cases(self, action):
        import os
        from pathlib import Path
        import worktree_protocol as protocol
        import worktree_preservation as preservation
        import worktree_pool as pool
        original = preservation.qualify
        native = preservation.git
        for prior_eviction in (False, True):
            for refused in (False, True):
                with self.subTest(action=action, prior_eviction=prior_eviction, refused=refused):
                    older, newer = self.pool_pair(suffix=action + str(prior_eviction) + str(refused))
                    later = newer.with_name(newer.name + "-later")
                    self.g(self.main, "worktree", "add", "-b", "lane/governance/" + later.name,
                           later, self.base)
                    with patch.dict(os.environ, GIT_COMMITTER_DATE="@1000000002 +0000"):
                        self.make_idle(later, self.base)
                    candidates = [older, newer, later]
                    failed = newer if prior_eviction else older
                    deferred = candidates[candidates.index(failed) + 1:]
                    reference = self.g(failed, "symbolic-ref", "HEAD").strip()
                    qualified, removals = [], []
                    cause = "initialization_in_progress" if refused else "fatal: final pool qualification broke"
                    def injected(source, path, stack=None):
                        if stack is not None:
                            qualified.append(Path(path))
                            if Path(path) == failed:
                                raise protocol.Refused(cause) if refused else protocol.GitFailure(cause)
                        return original(source, path, stack)
                    def record_remove(root, *args, **kwargs):
                        if args[:2] == ("worktree", "remove"):
                            removals.append(Path(args[-1]))
                        return native(root, *args, **kwargs)
                    if action == "return":
                        self.pool_github()
                        arguments = ["return", "--path", str(self.tree), "--pr", "42", "--writers-joined"]
                    else:
                        arguments = ["pool", "--dev", self.base, "--force"]
                    output = io.StringIO()
                    try:
                        with patch.object(pool, "available_fraction", return_value=0.04), \
                                patch.object(preservation, "qualify", side_effect=injected), \
                                patch.object(preservation, "git", side_effect=record_remove), \
                                patch.dict(os.environ, getattr(self, "pool_env", {})), redirect_stdout(output):
                            code = protocol.main(["--source", str(self.main)] + arguments)
                        self.assertEqual(74, code, output.getvalue())
                        result = json.loads(output.getvalue())
                        if action == "return":
                            self.assertIn(result["status"], ("returned", "already_idle"))
                            result = result["pool"]
                            deferred.append(self.tree)
                        self.assertEqual("failed", result["status"])
                        self.assertEqual([older] if prior_eviction else [], removals)
                        self.assertEqual(candidates[:candidates.index(failed) + 1], qualified)
                        rows = {row["path"]: row for row in result["items"]}
                        row = rows[str(failed)]
                        self.assertEqual("retained" if refused else "qualification_failed", row["outcome"])
                        self.assertEqual("remove", row["stage"])
                        self.assertIn(cause, row["reason"])
                        self.assertIn(cause, row["error"])
                        self.assertEqual(reference, row["branch"])
                        self.assertEqual(self.base, row["head"])
                        self.assertTrue(failed.is_dir())
                        for target in deferred:
                            self.assertTrue(target.is_dir())
                            self.assertEqual("retained", rows[str(target)]["outcome"])
                            self.assertEqual("idle_sweep_deferred", rows[str(target)]["reason"])
                        if prior_eviction:
                            self.assertEqual("removed", rows[str(older)]["outcome"])
                            self.assertEqual(self.base, rows[str(older)]["checkpoint"]["commit"])
                            self.assertTrue(rows[str(older)]["recovery_branch"])
                            self.assertFalse(older.exists())
                    finally:
                        for target in candidates:
                            if target.exists():
                                self.g(self.main, "worktree", "remove", target)
                        if not self.tree.exists():
                            self.g(self.main, "worktree", "add", self.tree, self.branch)
