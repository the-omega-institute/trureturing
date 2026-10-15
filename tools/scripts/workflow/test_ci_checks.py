"""Check execution, prerequisites, exit interpretation and complementary subsets."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import ci_checks as checks
import ci_contract as contract

ROOT = Path(__file__).resolve().parents[3]


class CheckTests(unittest.TestCase):
    def test_missing_executable_is_observable_infrastructure_failure(self):
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()) as output:
            code = checks.with_budget(Path(directory) / "budget", lambda: checks.execute(
                "restore", [str(Path(directory) / "missing")], compute=False))
        record = json.loads(output.getvalue().split("CI_CHECK ")[-1])
        self.assertEqual(code, 2)
        self.assertEqual(record["raw_exit"], 2)

    def test_failed_report_producer_probe_preserves_failure_without_raising(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "pull-request")
        with patch.object(checks.subprocess, "run", return_value=subprocess.CompletedProcess([], 2, "")), \
                patch.object(checks, "execute") as execute, contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_phase("lean-report", data, plan, "a" * 40, Path("changed")), 2)
        execute.assert_not_called()
        self.assertIn('"check":"lean-report","status":"failure","raw_exit":2', output.getvalue())

    def test_real_process_exit_three_is_special_only_for_delta(self):
        for raw in (0, 1, 2, 3, 124, 143):
            for delta in (False, True):
                with self.subTest(raw=raw, delta=delta), tempfile.TemporaryDirectory() as directory:
                    with contextlib.redirect_stdout(io.StringIO()) as output:
                        code = checks.with_budget(Path(directory) / "budget", lambda: checks.execute(
                            "delta" if delta else "unit", ["bash", "-c", "exit " + str(raw)], delta=delta))
                    record = json.loads(output.getvalue().split("CI_CHECK ")[-1])
                    self.assertEqual(record["raw_exit"], raw)
                    self.assertEqual(code, 0 if delta and raw == 3 else raw)
                    self.assertEqual(record["status"] == "protected-only", delta and raw == 3)

    def test_budget_is_not_reset_by_nested_shared_helpers(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "budget"
            with patch.dict(os.environ, {checks.ci_compute.BUDGET: str(path), checks.ci_compute.ACTIVE: "0"}):
                checks.ci_compute.initialize(path, 30)
                with self.assertRaises(FileExistsError):
                    checks.with_budget(path, lambda: 0)
                path.write_text("0")
                self.assertEqual(checks.execute("unit", ["bash", "-c", "exit 0"]), 124)

    def test_failed_judge_does_not_claim_dependent_checks_executed(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["tools/StrataLint.Lean/Changed.cs"], "pull-request")
        called = []
        def phase(name, *_):
            called.append(name)
            return 2 if name == "build-judge" else 0
        with patch.object(checks, "execute", return_value=0), patch.object(checks, "prepare_unit", return_value=0), \
                patch.object(checks, "current_phase", side_effect=phase), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 2)
        self.assertEqual(called, ["build-judge", "lean-report"])
        self.assertIn('"status":"blocked"', output.getvalue())

    def test_independent_validators_execute_after_a_semantic_rejection(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "pull-request")
        called = []
        def phase(name, *_):
            called.append(name)
            return 1 if name == "check-current" else 0
        with patch.object(checks, "execute", return_value=0), patch.object(checks, "prepare_unit", return_value=0), \
                patch.object(checks, "current_phase", side_effect=phase):
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 1)
        self.assertIn("scribe", called)
        self.assertIn("check-delta", called)

    def test_failed_dependency_preparation_blocks_actual_execution(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "pull-request")
        with patch.object(checks, "prepare_current", return_value=2), \
                patch.object(checks, "current_phase") as phase, contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 2)
        phase.assert_not_called()
        self.assertIn('"check":"lean-report","status":"blocked"', output.getvalue())

    def test_commands_keep_actual_canonical_test_evidence_and_complementary_filters(self):
        data, _ = contract.load(ROOT)
        with patch.object(checks, "execute", return_value=2) as execute:
            code = checks.unit_run("tests-lean", data["units"]["tests-lean"])
            self.assertEqual(code, 2)
            self.assertEqual(execute.call_args.args[1][:4], ["make", "-C", "tools", "test"])
            checks.unit_run("tests-declared-template", data["units"]["tests-declared-template"])
            self.assertIn('TEST_FILTER="FullyQualifiedName!~FourierBridgeSourceEvidenceTests"', execute.call_args.args[1][-1])
            plan = contract.selection(data, ["tools/StrataLint.Lean/Changed.cs"], "pull-request")
            checks.current_phase("source-evidence", data, plan, "a" * 40, Path("changed"))
            self.assertIn("TEST_FILTER=FullyQualifiedName~FourierBridgeSourceEvidenceTests", execute.call_args.args[1])


if __name__ == "__main__":
    unittest.main()
