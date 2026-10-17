"""Check execution, prerequisites, exit interpretation and complementary subsets."""
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
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
    def test_local_fib_ack_uses_actual_current_without_extra_preparation_or_suite(self):
        for current in (0, 1):
            with self.subTest(current=current), patch.dict(os.environ,
                    CI_CURRENT_RESULT="success", CI_CURRENT_UNIT="current"):
                result, calls, plan = self.local_spies(current=current,
                    paths=("tools/scripts/compiled-fib-test.sh",))
                self.assertEqual(result.returncode, current)
                self.assertTrue(plan["fib-regressions"])
                records = [json.loads(line[9:]) for line in result.stdout.splitlines() if line.startswith("CI_CHECK ")]
                ack = [r for r in records if r["check"] == "tests-fib"]
                self.assertEqual(len(ack), 1)
                self.assertEqual(ack[0]["status"], "success" if current == 0 else "blocked")
                self.assertFalse(any(call[:2] == ["make", "compiled-fib-test"] for call in calls))

    def test_standalone_fib_ack_has_no_current_success_and_emits_no_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output"
            environment = dict(os.environ, GITHUB_OUTPUT=str(output))
            environment.update(CI_CURRENT_RESULT="success", CI_CURRENT_UNIT="current")
            result = subprocess.run([sys.executable, "tools/scripts/workflow/ci_checks.py", "unit", "tests-fib"],
                cwd=ROOT, env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertFalse(output.exists())

    def test_report_selection_overrides_ambient_fib_selection_in_both_directions(self):
        data, _ = contract.load(ROOT)
        for path, selected in (("tools/scripts/compiled-fib-test.sh", True), ("Reg/D5/Owner.lean", False)):
            plan = contract.selection(data, [path], "pull-request")
            with self.subTest(path=path), patch.dict(os.environ, STRATALINT_FIB_REGRESSIONS_SELECTED=str(not selected).lower()), \
                    patch.object(checks.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "producer")), \
                    patch.object(checks, "execute", return_value=0) as execute:
                self.assertEqual(checks.current_phase("lean-report", data, plan, "a" * 40, Path("changed")), 0)
                self.assertEqual(execute.call_args.kwargs["env"]["STRATALINT_FIB_REGRESSIONS_SELECTED"], str(selected).lower())

    def test_fib_ack_requires_successful_current_identity_and_never_launches_suite(self):
        data, _ = contract.load(ROOT)
        unit = data["units"]["tests-fib"]
        for status, identity, expected in (("success", "current", 0), ("failure", "current", 1),
                ("cancelled", "current", 1), ("skipped", "current", 1), ("", "", 1),
                ("success", "wrong", 1)):
            with self.subTest(status=status, identity=identity), patch.dict(os.environ,
                    CI_CURRENT_RESULT=status, CI_CURRENT_UNIT=identity), patch.object(checks, "execute") as execute:
                self.assertEqual(checks.unit_run("tests-fib", unit, current=(status, identity)), expected)
                execute.assert_not_called()

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
                checks.ci_compute.initialize(path, 120)
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
        with patch.object(checks, "execute", return_value=0), patch.object(checks, "prepare_local_lean", return_value=0), patch.object(checks, "prepare_unit", return_value=0), \
                patch.object(checks, "current_phase", side_effect=phase):
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 1)
        self.assertIn("scribe", called)
        self.assertIn("check-delta", called)

    def test_failed_dependency_preparation_blocks_actual_execution(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "pull-request")
        with patch.object(checks, "prepare_judge", return_value=2), \
                patch.object(checks, "prepare_current", return_value=2), patch.object(checks, "prepare_local_lean", return_value=2), \
                patch.object(checks, "current_phase") as phase, contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 2)
        phase.assert_not_called()
        self.assertIn('"check":"lean-report","status":"blocked"', output.getvalue())

    def test_selected_evidence_restore_failure_keeps_other_ready_validators_reachable(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "pull-request")
        called = []
        with patch.object(checks, "prepare_current", return_value=2), \
                patch.object(checks, "prepare_local_lean", return_value=0), \
                patch.object(checks, "current_phase", side_effect=lambda phase, *_: called.append(phase) or 0):
            code = checks.current_run(data, plan, "a" * 40, Path("changed"), checks.Prerequisite(0, "accepted", True))
        self.assertEqual(2, code)
        self.assertNotIn("source-evidence", called)
        self.assertIn("lean-report", called)
        self.assertTrue({"scribe", "check-current", "check-delta", "compiled-audit"} <= set(called))

    def test_source_command_uses_original_current_delta_and_theory_scopes(self):
        data, _ = contract.load(ROOT)
        for paths, purpose, verb, delta in (
                (["D5/changed.lean"], "pull-request", "check-source", True),
                (["D5/changed.lean"], "push", "check-source", False),
                (["docs/develop/theory/Note.md"], "push", "check-delta", True),
                (["D5/changed.lean", "docs/develop/theory/Note.md"], "pull-request", "check-source", True)):
            plan = contract.selection(data, paths, purpose)
            with self.subTest(paths=paths, purpose=purpose), patch.object(checks, "execute", return_value=0) as execute:
                checks.current_phase("source", data, plan, "a" * 40, Path("changed"))
                command = execute.call_args.args[1]
                self.assertIn(verb, command)
                self.assertEqual(delta, "--protected-base" in command)
                self.assertNotIn("--candidate-lean-report", command)

    def test_source_rejection_blocks_every_guarded_launch_in_executable_local_adapter(self):
        result, calls, plan = self.local_spies(source=1)
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertTrue(plan["hits"]["current"])
        self.assertTrue(any("check-source" in call for call in calls))
        self.assertFalse(any(call[0] in ("elan", "make") for call in calls), calls)
        for unit, hit in plan["hits"].items():
            if hit and unit != "current":
                self.assertIn(f'"check":"{unit}","status":"blocked"', result.stdout)

    def test_unselected_current_theory_fast_path_and_push_do_not_gain_checks(self):
        result, calls, plan = self.local_spies(paths=("README.md",))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse(plan["hits"]["current"])
        self.assertFalse(any("check-source" in call or "check-delta" in call for call in calls))
        result, calls, plan = self.local_spies(paths=("docs/develop/theory/Note.md",), purpose="push")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertTrue(plan["theory"])
        self.assertFalse(any(call[0] == "elan" or call[:2] == ["make", "lean-report"] for call in calls))
        self.assertEqual(1, sum("check-delta" in call for call in calls))
        result, calls, plan = self.local_spies(purpose="push")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse(plan["delta"])
        self.assertFalse(any("check-delta" in call for call in calls))
        source = next(call for call in calls if "check-source" in call)
        self.assertNotIn("--protected-base", source)

    def test_success_and_later_rejection_preserve_all_selected_obligations(self):
        for current in (0, 1):
            with self.subTest(current=current):
                result, calls, plan = self.local_spies(source=0, current=current)
                self.assertEqual(current, result.returncode, result.stdout + result.stderr)
                records = [json.loads(line.removeprefix("CI_CHECK ")) for line in result.stdout.splitlines() if line.startswith("CI_CHECK ")]
                successful = {r["check"] for r in records if r["status"] == "success"}
                self.assertTrue({name for name, hit in plan["hits"].items() if hit and name != "current"} <= successful)
                self.assertTrue({"source-evidence", "scribe", "check-current", "check-delta", "compiled-audit"}
                                <= {r["check"] for r in records})
                self.assertIn("protected-only", {r["status"] for r in records})
                self.assertTrue(any(call[:2] == ["make", "lean-report"] for call in calls))

    def test_bootstrap_and_source_input_failures_preserve_independent_fallback(self):
        for source, judge in ((2, 0), (0, 1)):
            with self.subTest(source=source, judge=judge):
                result, calls, _ = self.local_spies(source=source, judge=judge)
                self.assertNotEqual(0, result.returncode)
                self.assertTrue(any(call[:2] == ["make", "lean-report"] for call in calls), calls)
                if judge:
                    self.assertFalse(any("check-source" in call for call in calls))
                    self.assertIn('"check":"check-current","status":"blocked"', result.stdout)
                self.assertTrue(any(call[:4] == ["make", "-C", "tools", "test"] for call in calls))

    def local_spies(self, source=0, current=0, judge=0, paths=("D5/changed.lean",), purpose="pull-request"):
        with tempfile.TemporaryDirectory(prefix="ci source with spaces ") as directory:
            root = Path(directory)
            scripts = root / "tools/scripts/workflow"
            scripts.mkdir(parents=True)
            for path in Path(__file__).parent.glob("*.py"):
                if not path.name.startswith("test_"):
                    shutil.copy2(path, scripts / path.name)
            (scripts / "judge-lean-producer.sh").write_text("#!/bin/bash\nexit 0\n")
            (scripts / "scribe-scope-paths.sh").write_text("#!/bin/bash\ncat \"$1\"\n")
            (scripts / "scribe-content-checks.sh").write_text("#!/bin/bash\nexit 0\n")
            (root / "Meta").mkdir()
            shutil.copy2(ROOT / contract.CONTRACT, root / contract.CONTRACT)
            data, _ = contract.load(ROOT)
            for unit in data["units"].values():
                for lock in unit["cache-dependency-path"].splitlines():
                    if not lock or "*" in lock:
                        continue
                    path = root / lock
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("{}")
                    (path.parent / (path.parent.name + ".csproj")).write_text("<Project />")
            (root / "lean-toolchain").write_text("fixture-pin\n")
            bindir = root / "bin"
            bindir.mkdir()
            code = (f"#!{sys.executable}\nimport json, os, sys\nfrom pathlib import Path\n"
                    "name=Path(sys.argv[0]).name; args=sys.argv[1:]\n"
                    "with open(os.environ['CALLS'],'a') as stream: stream.write(json.dumps([name,*args])+'\\n')\n"
                    "exitcode=0\n"
                    "if name=='dotnet':\n"
                    "    if 'check-source' in args: exitcode=int(os.environ['SOURCE'])\n"
                    "    elif 'check-current' in args: exitcode=int(os.environ['CURRENT'])\n"
                    "    elif 'check-delta' in args: exitcode=3\n"
                    "    elif args and args[0]=='build': exitcode=int(os.environ['JUDGE'])\n"
                    "sys.exit(exitcode)\n")
            for name in ("dotnet", "make", "elan"):
                path = bindir / name
                path.write_text(code)
                path.chmod(0o755)
            # Isolate the persistent host's tool location without modifying its
            # real home, installed toolchain or the production preparation owner.
            tool = root / "host/.elan/bin/elan"
            tool.parent.mkdir(parents=True)
            tool.write_text(code)
            tool.chmod(0o755)
            runner = root / "invoke.py"
            runner.write_text("import sys\nfrom pathlib import Path\n"
                              "sys.path.insert(0, str(Path(__file__).parent / 'tools/scripts/workflow'))\n"
                              "import ci_checks\n"
                              "ci_checks.Path.home = classmethod(lambda cls: Path(__file__).parent / 'host')\n"
                              "raise SystemExit(ci_checks.main())\n")
            def git(*args):
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base")
            for changed in paths:
                path = root / changed
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("candidate\n")
            env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ["PATH"], CALLS=str(root / "calls"),
                       SOURCE=str(source), CURRENT=str(current), JUDGE=str(judge), JUDGE_HIT="false",
                       STRATALINT_CI_COMPUTE_ACTIVE="0", PYTHONDONTWRITEBYTECODE="1")
            result = subprocess.run([sys.executable, str(runner), "local", "--base", "HEAD", "--purpose", purpose],
                                    cwd=root, env=env, capture_output=True, text=True, timeout=30)
            calls = [json.loads(line) for line in (root / "calls").read_text().splitlines()] if (root / "calls").exists() else []
            plan = json.loads(next(line.removeprefix("CI_LOCAL ") for line in result.stdout.splitlines() if line.startswith("CI_LOCAL ")))
            return result, calls, plan

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
