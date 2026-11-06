"""Native removal receipts and their compiled consumers, in private repositories."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import unittest
import uuid

SOURCE = Path(sys.argv[1]).resolve()
CONSUMER, FAULT = sys.argv[2:4]
del sys.argv[2:4]
from maintenance_log_tests import MaintenanceLogTests, LOG_ENV


class RemovalDiagnostics(MaintenanceLogTests):
    def test_consumed_failure(self):
        self.prepare_return_repository()
        from worktree_protocol import identity
        pool = CONSUMER in ("pool", "idle_cleanup")
        head = self.git("rev-parse", "HEAD").decode()
        paths = []
        for index in range(5 if pool else 3 if FAULT == "multiple" else 1):
            path = self.root / ("victim-" + str(index))
            if pool:
                token = uuid.uuid4().hex
                branch = "lane/governance/idle-" + token
                self.git("update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
                         "refs/heads/" + branch, head, "0" * len(head))
                self.git("worktree", "add", path, branch)
            else:
                self.git("worktree", "add", "-b", "lane/governance/victim-" + str(index), path)
            paths.append(path)
        victim = paths[0]
        branch = self.git("-C", victim, "symbolic-ref", "HEAD").decode()
        _, metadata = identity(self.main, victim)
        if CONSUMER == "expired_cleanup":
            env = dict(os.environ, GIT_AUTHOR_DATE="@1700000000 +0000", GIT_COMMITTER_DATE="@1700000000 +0000")
            subprocess.run(["git", "-C", str(victim), "commit", "--allow-empty", "-m", "expired"],
                           env=env, check=True, capture_output=True, timeout=15)
            head = self.git("-C", victim, "rev-parse", "HEAD").decode()
        # Direct checkpoint failures preserve outstanding ordinary bytes.
        if not pool:
            (victim / "unpublished").write_text("private ordinary bytes")
        binary = self.root / "bin"
        binary.mkdir()
        marker = self.root / "fault-triggered"
        ancestry = self.root / "ancestry-count"
        record = metadata / "worktree-removal"
        records = [str(identity(self.main, path)[1] / "worktree-removal") for path in paths]
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!/usr/bin/env python3
import os, pathlib, subprocess, sys
args = sys.argv[1:]
marker = pathlib.Path({str(marker)!r})
record = pathlib.Path({str(record)!r})
ancestry = pathlib.Path({str(ancestry)!r})
victim = {str(victim)!r}
fault = {FAULT!r}
if fault == "multiple":
    paths = {list(map(str, paths))!r}
    records = {records!r}
    for index, native_fault in enumerate(("qualification_failed", "checkpoint_failed", "partial_or_indeterminate")):
        trigger = (index == 0 and pathlib.Path(records[index]).exists() and "list" in args
            or index == 1 and "add" in args and paths[index] in args
            or index == 2 and "worktree" in args and "remove" in args and paths[index] in args)
        once = marker.with_name("trigger-" + str(index))
        if trigger and not once.exists():
            once.touch()
            marker.touch()
            print("private removal diagnostic " + paths[index], file=sys.stderr)
            sys.exit(1)
if fault != "multiple" and not marker.exists():
    count = int(ancestry.read_text()) if ancestry.exists() else 0
    is_ancestry = "merge-base" in args and "--is-ancestor" in args and victim in args
    if is_ancestry:
        count += 1
        ancestry.write_text(str(count))
    trigger = (fault == "checkpoint_failed" and "add" in args and victim in args
        or fault in ("qualification_failed", "refused") and record.exists() and "list" in args
        or fault == "partial_or_indeterminate" and "worktree" in args and "remove" in args and victim in args
        or fault == "revalidate" and is_ancestry and count == 2
        or fault == "inspect_refused" and is_ancestry and count == 1
        or fault == "inspect" and "status" in args and victim in args
        or fault == "inventory" and "worktree" in args and "list" in args)
    if trigger:
        marker.touch()
        if fault == "refused":
            subprocess.run([{real_git!r}, "-C", {str(self.main)!r}, "worktree", "lock", "--reason", "private removal lock", victim], check=True)
        else:
            print("private removal diagnostic " + victim, file=sys.stderr)
            sys.exit(2 if fault in ("revalidate", "inspect_refused") else 1)
os.execv({real_git!r}, [{real_git!r}, *args])
''')
        shim.chmod(0o755)
        cli = ["dotnet", str(SOURCE / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll")]
        native = [sys.executable, "-B", str(SOURCE / "tools/scripts/worktree/worktree_protocol.py"),
                  "--source", str(self.main)]
        command = (native + ["pool", "--dev", head, "--force"] if CONSUMER == "pool" else
                   native + ["remove", *[arg for path in paths for arg in ("--path", str(path))]] if CONSUMER == "remove" else
                   cli + ["worktree", "remove", "--names", " ".join(path.name for path in paths)] if CONSUMER == "explicit" else
                   cli + ["clean-lanes", "--lanes-only", "--force"])
        if FAULT != "pressure":
            result = subprocess.run(command, cwd=self.main, env=dict(self.environment,
                PATH=str(binary) + os.pathsep + self.environment["PATH"]),
                capture_output=True, text=True, timeout=45)
        if FAULT == "pressure":
            import io
            from contextlib import redirect_stdout
            from unittest.mock import patch
            import worktree_pool as owner
            import worktree_protocol as protocol
            output = io.StringIO()
            with patch.dict(os.environ, self.environment), redirect_stdout(output), patch.object(owner, "available_fraction",
                    side_effect=OSError("private removal diagnostic " + str(victim))):
                code = protocol.main(["--source", str(self.main), "pool", "--dev", head, "--force"])
            result = subprocess.CompletedProcess(command, code, output.getvalue(), "")
        else:
            self.assertTrue(marker.exists(), result.stdout + result.stderr)
        inspect_retention = FAULT == "inspect_refused"
        refused = FAULT == "refused" and not pool
        native_exit = 0 if inspect_retention else 68 if refused else 74
        expected_exit = 0 if CONSUMER.endswith("cleanup") else native_exit
        self.assertEqual(expected_exit, result.returncode, result.stdout + result.stderr)
        rows = self.rows("worktree-protocol")
        action = "pool" if pool else "remove"
        run = self.assert_single([row for row in rows if row["event"] == "run_started" and row["action"] == action])["run_id"]
        rows = [row for row in rows if row["run_id"] == run]
        final = rows[-1]
        self.assertEqual(("run_finished", action, native_exit),
                         (final["event"], final["action"], final["exit_code"]))
        self.assertTrue(victim.is_dir())
        self.assertEqual(branch, self.git("-C", victim, "symbolic-ref", "HEAD").decode())
        self.assertFalse(any("return_status" in row for row in rows))
        # Native output stays raw; compiled callers preserve its mapped diagnostic and recovery.
        receipt = json.loads(result.stdout) if CONSUMER in ("pool", "remove") else None
        if receipt is not None:
            self.assertEqual("worktree_pool" if pool else "worktree_removal", receipt["event"])
            self.assertEqual("succeeded" if inspect_retention else "refused" if refused else "failed", receipt["status"])
        if CONSUMER.endswith("cleanup"):
            output = [json.loads(line) for line in result.stdout.splitlines()]
            summary = output[-1]
            self.assertEqual(("clean_lanes_summary", "succeeded", "lanes_only"),
                             (summary["event"], summary["status"], summary["scope"]))
            item = self.assert_single([row for row in output if row.get("path") == str(victim)])
            self.assertEqual("idle_worktree" if pool else "lane_worktree" if refused else "stale_worktree", item["kind"])
            if not pool:
                self.assertEqual("head_commit_age", item["selection_reason"])
            if not inspect_retention:
                self.assertIn(str(victim), result.stderr)
        if CONSUMER == "explicit":
            self.assertIn("WORKTREE_REMOVE_RESULT exit=" + str(native_exit), result.stdout)
        if FAULT == "multiple":
            expected_outcomes = ["qualification_failed", "checkpoint_failed", "partial_or_indeterminate"]
            operations = [row for row in rows if row["event"] == "operation_finished"]
            self.assertEqual(expected_outcomes + ["failed"], [row["outcome"] for row in operations])
            self.assertEqual(expected_outcomes, [row["reason_code"] for row in operations[:-1]])
            self.assertEqual(["remove"] * 3, [row["stage"] for row in operations[:-1]])
            self.assertEqual(("failed", 3, "pool" if pool else "remove"),
                             (final["status"], final["failed_item_count"], final["stage"]))
            if receipt is not None:
                self.assertEqual(expected_outcomes, [item["outcome"] for item in receipt["items"][:3]])
            for index, path in enumerate(paths[:3]):
                self.assertTrue(path.is_dir())
                self.assertTrue((self.root / ("trigger-" + str(index))).exists())
                self.assertEqual(index != 1, Path(records[index]).exists())
                if index != 1:
                    recovery = json.loads(Path(records[index]).read_text())
                    self.assertEqual(recovery["commit"], self.git("rev-parse", recovery["recovery_branch"]).decode())
            if pool:
                self.assertFalse(paths[3].exists())
                self.assertTrue(paths[4].is_dir())
                self.assertEqual(["removed", "retained"], [item["outcome"] for item in receipt["items"][3:]])
            for path in paths:
                self.assertNotIn(str(path), json.dumps(rows))
            return
        if FAULT in ("qualification_failed", "checkpoint_failed", "partial_or_indeterminate"):
            self.assertIn("private removal diagnostic", result.stdout + result.stderr)
            failures = [row for row in rows if row["event"] == "operation_finished"]
            failure = self.assert_single(failures)
            keys = ("status", "outcome", "stage", "reason_code", "error_type")
            expected = ("failed", FAULT, "remove", FAULT, "CommandResult")
            self.assertEqual(expected, tuple(failure[key] for key in keys))
            self.assertEqual(expected, tuple(final[key] for key in keys))
            if pool:
                self.assertEqual("failed", failure["pool_status"])
                if receipt is not None and FAULT != "qualification_failed":
                    self.assertEqual("idle_capacity", self.assert_single([item for item in receipt["items"]
                        if item["path"] == str(victim)])["reason"])
            if receipt is not None:
                item = self.assert_single([item for item in receipt["items"] if item["path"] == str(victim)])
                self.assertEqual(FAULT, item["outcome"])
                self.assertNotIn("error_type", item)
                self.assertIn("private removal diagnostic", item["error"])
                if FAULT != "qualification_failed":
                    self.assertEqual(None if FAULT == "checkpoint_failed" else "unchanged" if pool else "committed",
                                     None if item["checkpoint"] is None else item["checkpoint"]["status"])
            self.assertEqual(FAULT != "checkpoint_failed", record.exists())
            if record.exists():
                recovery = json.loads(record.read_text())
                self.assertEqual(branch, recovery["recovery_branch"])
                self.assertEqual(recovery["commit"], self.git("rev-parse", branch).decode())
                if pool:
                    self.assertEqual(head, recovery["commit"])
                else:
                    self.assertEqual(b"private ordinary bytes", self.git("show", branch + ":unpublished"))
                if CONSUMER == "explicit" and FAULT == "partial_or_indeterminate":
                    self.assertIn(branch, result.stdout)
            elif not pool:
                self.assertEqual("private ordinary bytes", (victim / "unpublished").read_text())
        elif inspect_retention:
            self.assertEqual("succeeded", final["status"])
            self.assertFalse(any(row.get("status") == "failed" for row in rows))
            self.assertFalse(record.exists())
        elif refused:
            self.assertEqual(("refused", "refused", "Refused", "locked_recent"),
                             tuple(final[key] for key in ("status", "outcome", "error_type", "reason_code")))
            self.assertTrue(record.exists())
        else:
            stage = "remove" if FAULT == "refused" else "revalidate" if FAULT == "revalidate" else "disk_pressure" if FAULT == "pressure" else FAULT
            outcome = "retained" if FAULT in ("refused", "revalidate") else "failed" if FAULT in ("inventory", "pressure") else "sweep_failed"
            error_type = "Refused" if FAULT in ("refused", "revalidate") else "OSError" if FAULT == "pressure" else "GitFailure"
            self.assertEqual(("failed", stage, outcome, error_type),
                             tuple(final[key] for key in ("status", "stage", "outcome", "error_type")))
        persisted = json.dumps(rows)
        for private in ("private removal diagnostic", "private removal lock", str(victim)):
            self.assertNotIn(private, persisted)
        print(json.dumps(dict(consumer=CONSUMER, fault=FAULT, native_exit=native_exit,
                              caller_exit=result.returncode, status=final["status"], stage=final.get("stage"))))


if __name__ == "__main__":
    unittest.main(defaultTest="RemovalDiagnostics.test_consumed_failure")
