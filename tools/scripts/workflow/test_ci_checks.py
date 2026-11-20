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
                result, calls, plan = self.local_spies(source=current,
                    paths=("tools/scripts/compiled-fib-test.sh",))
                self.assertEqual(result.returncode, current)
                self.assertTrue(plan["fib-regressions"])
                records = [json.loads(line[9:]) for line in result.stdout.splitlines() if line.startswith("CI_CHECK ")]
                ack = [r for r in records if r["check"] == "tests-fib"]
                self.assertEqual(len(ack), 1)
                self.assertEqual(ack[0]["status"], "success" if current == 0 else "blocked")
                self.assertEqual(sum(call[:2] == ["make", "compiled-fib-test"] for call in calls), int(current == 0))

    def test_standalone_fib_ack_has_no_current_success_and_emits_no_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output"
            environment = dict(os.environ, GITHUB_OUTPUT=str(output))
            environment.update(CI_CURRENT_RESULT="success", CI_CURRENT_UNIT="current")
            result = subprocess.run([sys.executable, "tools/scripts/workflow/ci_checks.py", "unit", "tests-fib"],
                cwd=ROOT, env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertFalse(output.exists())

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

    def test_pr_and_push_use_the_same_scoped_command_with_ambient_full_build(self):
        for purpose in ("pull-request", "push"):
            with self.subTest(purpose=purpose):
                result, calls, _ = self.local_spies(purpose=purpose)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(["pr-lean", "D5/changed.lean"], calls)
                self.assertFalse(any(call[:2] == ["make", "lean-report"] for call in calls))

    def test_hosted_setup_uses_actual_targets_programs_and_selected_lean_suites(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["docs/develop/theory/Note.md"], "push")
        for targets, programs, suite, needs in (([], [], None, False), (["D5.A"], [], None, True),
                ([], ["Audit"], None, True), ([], [], "source-evidence", True),
                ([], [], "compiled-audit", True), ([], [], "fib-regressions", True)):
            with self.subTest(targets=targets, programs=programs, suite=suite), tempfile.TemporaryDirectory() as temp:
                scope = Path(temp) / "plan"
                output = Path(temp) / "output"
                scope.write_text(json.dumps({"targets": targets, "programs": programs}))
                chosen = dict(plan)
                if suite:
                    chosen[suite] = True
                with patch.object(checks, "execute", return_value=0), patch.dict(os.environ, GITHUB_OUTPUT=str(output)):
                    self.assertEqual(checks.current_phase("lean-plan", data, chosen, None, Path("changed"), scope), 0)
                self.assertEqual(output.read_text().splitlines(), [
                    "builds_lean=" + str(bool(targets or programs)).lower(), "needs_lean=" + str(needs).lower()])

    def test_failed_plan_blocks_setup_but_failed_ancillary_setup_still_runs_source_admission(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["tools/scripts/compiled-fib-test.sh"], "push")
        self.assertTrue(plan["fib-regressions"])
        for plan_code, prepared, runs_current in ((2, False, False), (0, True, True)):
            with self.subTest(plan_code=plan_code), patch.object(checks, "prepare_current", return_value=0), \
                    patch.object(checks, "prepare_lean_scope", return_value=(plan_code, False)), \
                    patch.object(checks, "prepare_local_lean", return_value=2) as setup, \
                    patch.object(checks, "current_phase", return_value=0) as phase:
                self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed"),
                    checks.Prerequisite(0, "accepted", True)), 2)
                self.assertEqual(setup.called, prepared)
                self.assertEqual([call.args[0] for call in phase.call_args_list], ["pr-lean"] if runs_current else [])

    def test_hosted_scope_rejects_missing_manifest_before_launch(self):
        data, revision = contract.load(ROOT)
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / "changed"
            command = ["ci_checks.py", "current", "pr-lean", "--purpose", "push",
                       "--changed", str(changed)]
            with patch.object(checks, "load", return_value=(data, revision)), \
                    patch.object(checks, "execute", return_value=0) as execute, \
                    patch.dict(os.environ, CI_BASE=""), patch.object(sys, "argv", command), \
                    contextlib.redirect_stderr(io.StringIO()) as error:
                self.assertEqual(checks.main(), 2)
                self.assertIn("missing changed-path manifest", error.getvalue())
                execute.assert_not_called()
                contract.write_paths(changed, ["D5/Changed.lean"])
                self.assertEqual(checks.main(), 2)
                command.extend(["--base", "b" * 40])
                self.assertEqual(checks.main(), 0)
                self.assertEqual(execute.call_args.args[1][-3:], [str(changed), "--protected-base", "b" * 40])

    def test_source_delta_uses_changed_paths_without_a_report(self):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/Changed.lean"], "pull-request")
        base = "a" * 40
        with patch.object(checks, "execute", return_value=0) as execute:
            self.assertEqual(checks.current_phase("check-delta", data, dict(plan, report=False), base, Path("changed")), 0)
            self.assertEqual(execute.call_args.args[1], ["dotnet", checks.CLI, "check-delta", "--protected-base", base,
                                                      "--changed-paths-from", "changed"])
            self.assertTrue(execute.call_args.kwargs["delta"])

    def test_admission_reuses_all_batches_and_runs_without_reports_for_source_changes(self):
        import ci_pr_lean
        cases = [([], 0, 3, 0), (["D5.A", "D5.B"], 1, 0, 1), (["D5.A"], 0, 2, 2)]
        for targets, current_exit, delta_exit, expected in cases:
            with self.subTest(targets=targets), tempfile.TemporaryDirectory() as temp:
                changed = Path(temp) / "changed"
                contract.write_paths(changed, ["some-file"])
                built, consumers = [], []
                def run(command, **options):
                    if "lean-inputs" in command:
                        plan = {"programs": [], "targets": targets, "paths": [], "definitions": {}}
                        return subprocess.CompletedProcess(command, 0, json.dumps(plan))
                    if command[:2] == ["make", "lean-report-scoped"]:
                        report = Path(options["env"]["LEAN_REPORT"])
                        self.assertNotIn(report, built)
                        report.touch()
                        built.append(report)
                    if command[2] in ("check-current", "check-delta"):
                        consumers.append(command[2])
                        manifest = Path(command[command.index("--changed-paths-from") + 1])
                        self.assertEqual(contract.read_changed(manifest), ["some-file"])
                        reports = Path(command[command.index("--scoped-reports-from") + 1])
                        self.assertEqual(reports.read_bytes(), b"".join(os.fsencode(p) + b"\0" for p in built))
                        self.assertTrue(all(path.is_file() for path in built))
                        return subprocess.CompletedProcess(command, current_exit if command[2] == "check-current" else delta_exit)
                    return subprocess.CompletedProcess(command, 0)
                scope_file = Path(temp) / "scope"
                scope_file.write_text(json.dumps({"programs": [], "targets": targets, "paths": [], "definitions": {}}))
                with patch.object(ci_pr_lean, "plan_scope", side_effect=AssertionError("scope planned twice")), \
                        patch.object(ci_pr_lean.subprocess, "run", side_effect=run), \
                        patch.object(ci_pr_lean, "report_batches", return_value=[([target], []) for target in targets]):
                    self.assertEqual(ci_pr_lean.check(changed, "a" * 40, scope_file), expected)
                self.assertEqual(consumers, ["check-current", "check-delta"])
                self.assertEqual(len(built), len(targets))

    def test_real_process_exits_are_preserved(self):
        for raw in (0, 1, 2, 3, 124, 143):
            with self.subTest(raw=raw), tempfile.TemporaryDirectory() as directory:
                with contextlib.redirect_stdout(io.StringIO()) as output:
                    code = checks.with_budget(Path(directory) / "budget", lambda: checks.execute(
                        "unit", ["bash", "-c", "exit " + str(raw)]))
                record = json.loads(output.getvalue().split("CI_CHECK ")[-1])
                self.assertEqual(record["raw_exit"], raw)
                self.assertEqual(code, raw)

    def test_budget_is_not_reset_by_nested_shared_helpers(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "budget"
            with patch.dict(os.environ, {checks.ci_compute.BUDGET: str(path), checks.ci_compute.ACTIVE: "0"}):
                checks.ci_compute.initialize(path, 120)
                with self.assertRaises(FileExistsError):
                    checks.with_budget(path, lambda: 0)
                path.write_text("0")
                self.assertEqual(checks.execute("unit", ["bash", "-c", "exit 0"]), 124)

    @patch.object(checks, "prepare_lean_scope", return_value=(0, True))
    def test_failed_judge_does_not_claim_dependent_checks_executed(self, _):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["tools/StrataLint.Lean/Changed.cs"], "push")
        called = []
        def phase(name, *_):
            called.append(name)
            return 2 if name == "build-judge" else 0
        with patch.object(checks, "execute", return_value=0), patch.object(checks, "prepare_unit", return_value=0), \
                patch.object(checks, "current_phase", side_effect=phase), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 2)
        self.assertEqual(called, ["build-judge", "pr-lean"])
        self.assertIn('"status":"blocked"', output.getvalue())

    @patch.object(checks, "prepare_lean_scope", return_value=(0, True))
    def test_independent_validators_execute_after_a_semantic_rejection(self, _):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "push")
        called = []
        def phase(name, *_):
            called.append(name)
            return 1 if name == "source-evidence" else 0
        with patch.object(checks, "execute", return_value=0), patch.object(checks, "prepare_local_lean", return_value=0), patch.object(checks, "prepare_unit", return_value=0), \
                patch.object(checks, "current_phase", side_effect=phase):
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 1)
        self.assertIn("source-evidence", called)
        self.assertIn("compiled-audit", called)

    @patch.object(checks, "prepare_lean_scope", return_value=(0, True))
    def test_failed_dependency_preparation_blocks_actual_execution(self, _):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "push")
        with patch.object(checks, "prepare_judge", return_value=2), \
                patch.object(checks, "prepare_current", return_value=2), patch.object(checks, "prepare_local_lean", return_value=2), \
                patch.object(checks, "current_phase") as phase, contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(checks.current_run(data, plan, "a" * 40, Path("changed")), 2)
        phase.assert_not_called()
        self.assertIn('"check":"pr-lean","status":"blocked"', output.getvalue())

    @patch.object(checks, "prepare_lean_scope", return_value=(0, True))
    def test_selected_evidence_restore_failure_keeps_other_ready_validators_reachable(self, _):
        data, _ = contract.load(ROOT)
        plan = contract.selection(data, ["D5/changed.lean"], "push")
        called = []
        with patch.object(checks, "prepare_current", return_value=2), \
                patch.object(checks, "prepare_local_lean", return_value=0), \
                patch.object(checks, "current_phase", side_effect=lambda phase, *_: called.append(phase) or 0):
            code = checks.current_run(data, plan, "a" * 40, Path("changed"), checks.Prerequisite(0, "accepted", True))
        self.assertEqual(2, code)
        self.assertNotIn("source-evidence", called)
        self.assertEqual(called, ["pr-lean", "compiled-audit"])

    def test_source_command_uses_original_current_delta_and_theory_scopes(self):
        data, _ = contract.load(ROOT)
        for paths, purpose, verb, delta in (
                (["D5/changed.lean"], "pull-request", "check-source", True),
                (["D5/changed.lean"], "push", "check-source", True),
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

    def test_readme_skips_current_and_theory_path_keeps_pr_selection(self):
        for purpose in ("pull-request", "push"):
            with self.subTest(purpose=purpose):
                result, calls, plan = self.local_spies(paths=("README.md",), purpose=purpose)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertFalse(plan["hits"]["current"])
                self.assertFalse(any("check-source" in call for call in calls))
                result, calls, plan = self.local_spies(paths=("docs/develop/theory/Note.md",), purpose=purpose)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertTrue(plan["hits"]["current"])
                self.assertTrue(plan["report"])
                self.assertTrue(plan["delta"])
                source = next(call for call in calls if "check-source" in call)
                self.assertIn("--protected-base", source)
                self.assertIn(["pr-lean", "docs/develop/theory/Note.md"], calls)
                self.assertFalse(any(call[0] == "elan" for call in calls))
                self.assertEqual(sum(call[0] == "lean-plan" for call in calls), 1)

    def test_scoped_failure_is_red_and_blocks_report_consumers_only(self):
        for scoped in (0, 1):
            with self.subTest(scoped=scoped):
                result, calls, plan = self.local_spies(scoped=scoped, purpose="push")
                self.assertEqual(scoped, result.returncode, result.stdout + result.stderr)
                records = {record["check"]: record["status"] for record in (
                    json.loads(line.removeprefix("CI_CHECK ")) for line in result.stdout.splitlines()
                    if line.startswith("CI_CHECK "))}
                self.assertTrue(all(records[name] == "success" for name, hit in plan["hits"].items()
                                    if hit and name != "current"))
                for phase in ("source-evidence", "compiled-audit"):
                    self.assertEqual(records[phase], "blocked" if scoped else "success")
                self.assertIn(["pr-lean", "D5/changed.lean"], calls)

    def test_bootstrap_and_source_input_failures_preserve_independent_fallback(self):
        for source, judge in ((2, 0), (0, 1)):
            with self.subTest(source=source, judge=judge):
                result, calls, _ = self.local_spies(source=source, judge=judge, purpose="push")
                self.assertNotEqual(0, result.returncode)
                self.assertIn(["pr-lean", "D5/changed.lean"], calls)
                if judge:
                    self.assertFalse(any("check-source" in call for call in calls))
                    self.assertIn('"check":"compiled-audit","status":"blocked"', result.stdout)
                self.assertTrue(any(call[:4] == ["make", "-C", "tools", "test"] for call in calls))

    def local_spies(self, source=0, scoped=0, judge=0, paths=("D5/changed.lean",), purpose="pull-request"):
        with tempfile.TemporaryDirectory(prefix="ci source with spaces ") as directory:
            root = Path(directory)
            scripts = root / "tools/scripts/workflow"
            scripts.mkdir(parents=True)
            for path in Path(__file__).parent.glob("*.py"):
                if not path.name.startswith("test_"):
                    shutil.copy2(path, scripts / path.name)
            (scripts / "ci_pr_lean.py").write_text(
                "import json, os, sys\nfrom pathlib import Path\nfrom ci_contract import read_changed\n"
                "paths = read_changed(Path(sys.argv[1]))\n"
                "planning = '--write-plan' in sys.argv\n"
                "with open(os.environ['CALLS'], 'a') as output:\n"
                "    output.write(json.dumps(['lean-plan' if planning else 'pr-lean', *paths]) + '\\n')\n"
                "if planning:\n"
                "    Path(sys.argv[-1]).write_text(json.dumps({'programs': [], 'targets': [p for p in paths if p.endswith('.lean')]}))\n"
                "    sys.exit(0)\n"
                "sys.exit(int(os.environ['SCOPED']))\n")
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
            env = dict(os.environ, FULL_BUILD="1", PATH=str(bindir) + os.pathsep + os.environ["PATH"], CALLS=str(root / "calls"),
                       SOURCE=str(source), SCOPED=str(scoped), JUDGE=str(judge), JUDGE_HIT="false",
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


class ScopedReportTests(unittest.TestCase):
    def test_empty_scope_has_no_build_and_large_scopes_keep_scribe_inputs_together(self):
        from ci_pr_lean import report_batches
        self.assertEqual(list(report_batches({"targets": []})), [])
        scope = {"targets": ["D5.A", "D5.B", "Reg.Z"], "paths": ["Blueprint/doc.scribe.cs"],
                 "definitions": {"Blueprint/doc.scribe.cs": ["D5.A", "D5.B"]}}
        self.assertEqual(list(report_batches(scope, limit=10)),
                         [(["D5.A", "D5.B"], ["Blueprint/doc.scribe.cs"]), (["Reg.Z"], [])])


if __name__ == "__main__":
    unittest.main()
