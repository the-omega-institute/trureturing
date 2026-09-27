"""Behavioral contract for CI console presentation; raw evidence is independent."""
import io
import json
import os
import pathlib
import select
import signal
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools/scripts"))
import ci_output


class PresentationTests(unittest.TestCase):
    def setUp(self):
        self.now = 0
        self.output = io.StringIO()
        self.presenter = ci_output.Presenter("current", self.output, interval=30, clock=lambda: self.now)

    def test_information_is_counted_only_at_intervals_even_when_idle(self):
        for index in range(1000):
            self.presenter.line(f"information: checked module {index}\n", "stdout")
        self.presenter.tick()
        self.assertEqual("", self.output.getvalue())
        self.now = 30
        self.presenter.tick()
        self.assertIn("information=1000", self.output.getvalue())
        self.assertIn("checked module 999", self.output.getvalue())
        self.assertNotIn("checked module 998", self.output.getvalue())
        self.assertIn("new_information=1000", self.output.getvalue())
        self.now = 90
        self.presenter.tick()
        self.assertEqual(2, len(self.output.getvalue().splitlines()))
        self.assertIn("new_information=0", self.output.getvalue().splitlines()[-1])

    def test_xunit_failure_context_summarizes_embedded_information_and_keeps_details(self):
        prefix = "[xUnit.net 00:00:02.60]       "
        lines = [
            prefix + "Tests.InformationIsPeriodic [FAIL]",
            prefix + "information: CI_LOG_PROBE_ACTIVITY 0",
            prefix + '{"level":"information","message":"embedded structured activity"}',
            prefix + "unlabelled assertion detail",
            prefix + "warning: CI_LOG_PROBE_WARNING",
            prefix + "  CI_LOG_PROBE_WARNING_DETAIL",
            prefix + "error: CI_LOG_PROBE_ERROR",
            prefix + "  CI_LOG_PROBE_ERROR_DETAIL",
        ]
        for line in lines:
            self.presenter.line(line + "\n", "stdout")
        rendered = self.output.getvalue()
        self.assertNotIn("CI_LOG_PROBE_ACTIVITY", rendered)
        self.assertNotIn("embedded structured activity", rendered)
        for line in [lines[0], *lines[3:]]:
            self.assertIn(line, rendered)
        self.assertEqual(2, self.presenter.counts["information"])
        self.presenter.line(prefix + "Finished: Tests\n", "stdout")
        self.presenter.line("ordinary progress after tests\n", "stdout")
        self.assertNotIn("ordinary progress after tests", self.output.getvalue())

    def test_xunit_captured_boundaries_preserve_the_outer_step_and_failure_details(self):
        prefix = "[xUnit.net 00:00:02.60]       "
        for boundaries in [
            ['STAGE_STEP {"name":"restore","status":"started"}'],
            ['STAGE_PROCESS {"child_exit":{"code":0}}'],
            ['CI_DIAGNOSTIC_BEGIN stage=current', 'CI_DIAGNOSTIC_END'],
        ]:
            with self.subTest(boundaries=boundaries):
                output = io.StringIO()
                presenter = ci_output.Presenter("engineering", output)
                presenter.line('STAGE_STEP {"name":"tests","status":"started"}\n', "stdout")
                for line in ["Tests.ActualFailure [FAIL]", *boundaries,
                             "unlabelled assertion detail", "  at Tests.ActualFailure()"]:
                    presenter.line(prefix + line + "\n", "stdout")
                self.assertIn(prefix + "unlabelled assertion detail", output.getvalue())
                self.assertIn(prefix + "  at Tests.ActualFailure()", output.getvalue())
                self.assertEqual("tests", presenter.step)
                self.assertEqual(0, presenter.block_depth.get("stdout", 0))

    def test_periodic_progress_tracks_work_done_not_just_log_volume(self):
        self.presenter.line('STAGE_STEP {"name":"lean-report","status":"started"}\n', "stdout")
        self.presenter.line("ℹ [348/1000] Built D5.Foo\n", "stdout")
        self.now = 30
        self.presenter.tick()
        self.assertIn("step=lean-report", self.output.getvalue())
        self.assertIn("348/1000", self.output.getvalue())
        self.presenter.line("✔ [400/1000] Built D5.Bar\n", "stdout")
        self.presenter.line('RESOURCE_OBSERVATION {"phase":"sample","rss_peak_kb":1000}\n', "stdout")
        self.now = 60
        self.presenter.tick()
        latest = self.output.getvalue().splitlines()[-1]
        self.assertIn("400/1000", latest)
        self.assertIn("progress=[400/1000]", latest)
        self.assertIn("elapsed=60s", latest)

    def test_resource_heartbeats_keep_the_latest_work_activity_visible(self):
        self.presenter.line('STAGE_STEP {"name":"check-current","status":"started"}\n', "stdout")
        self.presenter.line("CURRENT_FINALIZE phase=seal status=started\n", "stdout")
        self.presenter.line("RESOURCE_SAMPLE sequence=20 phase=periodic\n", "stdout")
        self.presenter.line('RESOURCE_OBSERVATION {"phase":"sample"}\n', "stdout")
        self.now = 30
        self.presenter.tick()
        self.assertIn('latest="CURRENT_FINALIZE phase=seal status=started"', self.output.getvalue())
        self.assertIn("information=4", self.output.getvalue())

    def test_warnings_and_errors_keep_multiline_details_immediately(self):
        messages = ["warning: D5/Foo.lean:4: unused variable\n", "  variable x\n",
                    "more detail without indentation\n", "error: D5/Foo.lean:9: type mismatch\n",
                    "expected Nat\n", "\n", "but got Bool\n"]
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())
        self.presenter.line("information: next operation\n", "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_stderr_information_is_summarized_but_unclassified_diagnostics_survive(self):
        self.presenter.line("info: downloading packages\n", "stderr")
        self.presenter.line("Unhandled exception. System.IO.IOException: broken pipe\n", "stderr")
        self.presenter.line("   at Worker.Run()\n", "stderr")
        self.assertNotIn("downloading", self.output.getvalue())
        self.assertIn("broken pipe\n   at Worker.Run()", self.output.getvalue())

    def test_structured_diagnostics_use_severity_and_keep_all_fields(self):
        warning = {"DisplaySeverity": 1, "RuleId": {"Value": "SL-003"}, "Path": "D5/Foo.lean",
                   "Message": "line one\nline two", "AdmissionEffect": 0}
        error = {"DisplaySeverity": 2, "Message": "blocked", "Path": "D5/Bar.lean"}
        self.presenter.line(json.dumps({"diagnostics": [
            {"DisplaySeverity": 0, "Message": "quiet information"}, warning, error]}) + "\n", "stdout")
        rendered = self.output.getvalue()
        self.assertNotIn("quiet information", rendered)
        self.assertIn("D5/Foo.lean", rendered)
        self.assertIn("SL-003", rendered)
        self.assertIn("line one\\nline two", rendered)
        self.assertIn("blocked", rendered)

    def test_compact_json_information_uses_its_explicit_severity(self):
        self.presenter.line('{"severity":"information","message":"error:example"}\n', "stdout")
        self.assertEqual("", self.output.getvalue())
        self.assertEqual(1, self.presenter.counts["information"])

    def test_progress_records_and_success_json_do_not_leak(self):
        self.presenter.line('STAGE_STEP {"stage":"current","name":"lean-report","status":"started"}\n', "stdout")
        self.presenter.line('{"stage":"current","exit":0,"error":null,"scope":{"paths":["huge-list"]}}\n', "stdout")
        self.assertEqual("", self.output.getvalue())
        self.presenter.finish(0)
        self.assertIn("step=lean-report", self.output.getvalue())
        self.assertIn("exit=0", self.output.getvalue())
        self.assertNotIn("huge-list", self.output.getvalue())

    def test_progress_on_stderr_is_information_and_large_messages_are_bounded(self):
        self.presenter.line("⣷ [123/456] Building a module\n", "stderr")
        self.assertEqual("", self.output.getvalue())
        self.now = 30
        self.presenter.tick()
        self.assertIn("123/456", self.output.getvalue())
        self.presenter.line("info: " + "x" * 10000 + "\n", "stdout")
        self.presenter.finish(0)
        self.assertLess(len(self.output.getvalue().splitlines()[-1]), 500)

    def test_failure_json_is_detailed_without_dumping_successful_scope(self):
        self.presenter.line('{"stage":"current","exit":2,"error":"cannot read report", "scope":{"paths":["noise"]}}\n', "stdout")
        self.assertIn("cannot read report", self.output.getvalue())
        self.assertNotIn("noise", self.output.getvalue())

    def test_ansi_severity_and_github_annotations_are_preserved(self):
        messages = ["\x1b[33mwarning: coloured diagnostic\x1b[0m\n",
                    "::error file=foo,line=3::annotation detail\n"]
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_compiler_codes_and_plain_warning_labels_are_detailed(self):
        messages = ["Foo.cs(3,4): warning CS0168: unused variable\n",
                    "Foo.cs(3,4): error CS1002: expected semicolon\n",
                    "WARNING donor cache is stale\n", "[ERROR] command failed\n"]
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_diagnostic_continuations_are_not_progress_or_event_records(self):
        messages = ["error: a constraint failed\n", "EXPECTED 100% coverage\n", "got [3/4] entries\n",
                    '{"expected":4,"actual":3}\n']
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_repository_failure_sentinels_are_errors(self):
        message = "INFRASTRUCTURE_FAILURE cannot acquire report\n"
        self.presenter.line(message, "stdout")
        self.assertEqual(message, self.output.getvalue())

    def test_successful_build_and_test_progress_after_warning_is_summarized(self):
        self.presenter.line("foo.cs(1,1): warning CS0168: unused variable\n", "stdout")
        self.presenter.line("Foo -> bin/Release/Foo.dll\n", "stdout")
        self.presenter.line("Build succeeded.\n", "stdout")
        self.presenter.line("  Passed MyTest [12 ms]\n", "stdout")
        self.assertEqual("foo.cs(1,1): warning CS0168: unused variable\n", self.output.getvalue())

    def test_lean_spinner_after_warning_resumes_periodic_progress(self):
        self.presenter.line("warning: unused variable\n", "stdout")
        self.presenter.line("⣷ [2/10] Building D5.Bar\n", "stdout")
        self.assertEqual("warning: unused variable\n", self.output.getvalue())
        self.now = 30
        self.presenter.tick()
        self.assertIn("progress=[2/10]", self.output.getvalue())

    def test_failed_command_block_preserves_unlabelled_details(self):
        messages = ["CI_DIAGNOSTIC_BEGIN step=restore raw_exit=155\n", "No .NET SDKs were found.\n",
                    '{"detail":"cannot start"}\n', "CI_DIAGNOSTIC_END\n"]
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())
        self.presenter.line("info: finishing\n", "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_failure_block_summarizes_information_and_preserves_error_details(self):
        self.presenter.line("CI_DIAGNOSTIC_BEGIN step=build raw_exit=1\n", "stdout")
        for index in range(2000):
            self.presenter.line(f"information: checked module {index}\n", "stdout")
        self.presenter.line("error: type mismatch\n", "stdout")
        self.presenter.line("expected Nat\n", "stdout")
        self.presenter.line("CI_DIAGNOSTIC_END\n", "stdout")
        self.assertNotIn("checked module", self.output.getvalue())
        self.assertIn("error: type mismatch\nexpected Nat\n", self.output.getvalue())
        self.now = 30
        self.presenter.tick()
        self.assertIn("information=2000", self.output.getvalue())

    def test_failed_test_replay_summarizes_framework_progress_and_success_totals(self):
        self.presenter.line("CI_DIAGNOSTIC_BEGIN step=tests raw_exit=1\n", "stdout")
        messages = ["VSTest version 18.7.0 (arm64)",
                    "[xUnit.net 00:00:00.00] xUnit.net VSTest Adapter v3.1.4",
                    "[xUnit.net 00:00:00.16]   Discovering: Tests",
                    "[xUnit.net 00:00:00.22]   Discovered:  Tests",
                    "[xUnit.net 00:00:00.25]   Starting:    Tests",
                    "[xUnit.net 00:01:57.24]   Finished:    Tests",
                    "Test Run Successful.", "Total tests: 55", "     Passed: 55", " Total time: 1.9636 Minutes"]
        for line in messages:
            self.presenter.line(line + "\n", "stdout")
        self.assertEqual("CI_DIAGNOSTIC_BEGIN step=tests raw_exit=1\n", self.output.getvalue())
        failure = ["[xUnit.net 00:02:20.26] Tests.ActualFailure [FAIL]\n",
                   "Test Run Failed.\n", "Failed: 1\n", "  Stack Trace:\n", "    at Tests.ActualFailure()\n"]
        for line in failure:
            self.presenter.line(line, "stdout")
        self.assertIn("".join(failure), self.output.getvalue())
        self.assertEqual(len(messages), self.presenter.counts["information"])

    def test_resource_samples_do_not_interrupt_warning_context(self):
        self.presenter.line("warning: diagnostic\n", "stdout")
        self.presenter.line("RESOURCE_SAMPLE sequence=1 phase=periodic\n", "stdout")
        self.presenter.line("  first detail\n", "stdout")
        self.presenter.line('RESOURCE_OBSERVATION {"phase":"sample"}\n', "stdout")
        self.presenter.line("  second detail\n", "stdout")
        self.presenter.line("information: next operation\n", "stdout")
        self.assertEqual("warning: diagnostic\n  first detail\n  second detail\n", self.output.getvalue())

    def test_lean_variable_named_info_does_not_hide_goal_context(self):
        messages = ["error: unsolved goals\n", "info : Nat\n", "⊢ info = 0\n"]
        for line in messages:
            self.presenter.line(line, "stdout")
        self.assertEqual("".join(messages), self.output.getvalue())

    def test_restore_activity_after_warning_returns_to_summary(self):
        self.presenter.line("Foo.csproj : warning NU1901: package vulnerability\n", "stdout")
        for index in range(100):
            self.presenter.line(f"  Restored /src/Project{index}.csproj (in 20 ms).\n", "stdout")
        self.assertNotIn("Restored", self.output.getvalue())
        self.now = 30
        self.presenter.tick()
        self.assertIn("information=100", self.output.getvalue())

    def test_failed_operation_metadata_preserves_following_explanation(self):
        self.presenter.line('STAGE_PROCESS {"stage":"engineering","child_exit":{"code":155}}\n', "stdout")
        self.presenter.line("No .NET SDKs were found.\n", "stdout")
        self.presenter.line("Install a .NET SDK to run this application.\n", "stdout")
        self.assertIn("No .NET SDKs were found.\nInstall a .NET SDK", self.output.getvalue())

    def test_failed_operation_context_survives_information_until_next_step(self):
        for result in ({"child_exit": {"code": 155}}, {"outcome": "cancelled", "child_exit": {"code": 0}}):
            with self.subTest(result=result):
                output = io.StringIO()
                presenter = ci_output.Presenter("engineering", output)
                presenter.line("STAGE_PROCESS " + json.dumps(result) + "\n", "stdout")
                presenter.line("information: host initialization\n", "stdout")
                presenter.line("No .NET SDKs were found.\n", "stdout")
                presenter.line('STAGE_STEP {"name":"next","status":"started"}\n', "stdout")
                presenter.line("ordinary activity in next step\n", "stdout")
                self.assertIn("No .NET SDKs were found.", output.getvalue())
                self.assertNotIn("host initialization", output.getvalue())
                self.assertNotIn("ordinary activity", output.getvalue())

    def test_diagnostic_json_keeps_outer_severity_and_unclassified_failure_fields(self):
        messages = ['error: {"stage":"check","detail":"cannot load required input"}\n',
                    '{"stage":"check","detail":"failed input path"}\n']
        for block in (False, True):
            with self.subTest(block=block):
                output = io.StringIO()
                presenter = ci_output.Presenter("current", output)
                if block:
                    presenter.line("CI_DIAGNOSTIC_BEGIN step=check raw_exit=1\n", "stdout")
                for line in messages:
                    presenter.line(line, "stdout")
                self.assertIn("".join(messages), output.getvalue())

    def test_failure_blocks_keep_context_across_nested_operation_boundaries(self):
        for boundary in ('STAGE_STEP {"name":"restore","status":"started"}\n',
                         'STAGE_PROCESS {"child_exit":{"code":0}}\n'):
            with self.subTest(boundary=boundary):
                output = io.StringIO()
                presenter = ci_output.Presenter("engineering", output)
                for line in ("CI_DIAGNOSTIC_BEGIN step=tests raw_exit=1\n", boundary,
                             "No .NET SDKs were found.\n", "information: finishing\n", "CI_DIAGNOSTIC_END\n"):
                    presenter.line(line, "stdout")
                self.assertIn("No .NET SDKs were found.", output.getvalue())
                self.assertIn("CI_DIAGNOSTIC_END", output.getvalue())
                self.assertNotIn("information: finishing", output.getvalue())

    def test_nested_diagnostic_block_end_keeps_outer_context(self):
        for line in ("CI_DIAGNOSTIC_BEGIN step=tests raw_exit=1\n",
                     "CI_DIAGNOSTIC_BEGIN step=nested raw_exit=1\n",
                     "inner explanation\n", "CI_DIAGNOSTIC_END\n",
                     'STAGE_PROCESS {"child_exit":{"code":0}}\n',
                     "outer explanation\n", "CI_DIAGNOSTIC_END\n", "ordinary activity\n"):
            self.presenter.line(line, "stdout")
        self.assertIn("inner explanation", self.output.getvalue())
        self.assertIn("outer explanation", self.output.getvalue())
        self.assertNotIn("ordinary activity", self.output.getvalue())


class ProcessTests(unittest.TestCase):
    def run_child(self, code, **env):
        with tempfile.TemporaryDirectory() as directory:
            log = pathlib.Path(directory) / "raw.log"
            result = subprocess.run([sys.executable, "-B", str(ROOT / "tools/scripts/ci_output.py"),
                                     "--stage", "build", "--log", str(log), "--",
                                     sys.executable, "-u", "-c", code],
                                    env={**os.environ, "CI_LOG_INTERVAL_SECONDS": "30", **env}, capture_output=True, text=True, timeout=30)
            return result, log.read_text() if log.exists() else ""

    def test_short_stage_final_summary_raw_log_and_exit_are_preserved(self):
        result, raw = self.run_child("import sys; print('information: compiling'); print('warning: detail'); sys.exit(7)")
        self.assertEqual(7, result.returncode, result.stderr)
        self.assertIn("warning: detail", result.stdout)
        self.assertIn("exit=7", result.stdout)
        self.assertIn("information: compiling", raw)

    def test_failed_child_without_severity_replays_complete_failure_output(self):
        result, raw = self.run_child("import sys; print('unlabelled failure context', end=''); sys.exit(9)")
        self.assertEqual(9, result.returncode, result.stderr)
        self.assertIn("unlabelled failure context", result.stdout)
        self.assertEqual("unlabelled failure context", raw)

    def test_failure_fallback_does_not_replay_information(self):
        result, raw = self.run_child("import sys; print('information: compiling'); print('unlabelled failure context'); sys.exit(9)")
        self.assertEqual(9, result.returncode, result.stderr)
        self.assertIn("unlabelled failure context", result.stdout)
        self.assertNotIn("\ninformation: compiling\n", result.stdout)
        self.assertIn("information: compiling", raw)

    def test_failure_fallback_preserves_details_after_operation_boundaries(self):
        lines = ['STAGE_STEP {"name":"restore","status":"started"}',
                 "No .NET SDKs were found.", "Install a .NET SDK to run this application.",
                 "information: finishing"]
        result, raw = self.run_child("import sys; print(" + repr("\n".join(lines)) + "); sys.exit(9)")
        self.assertEqual(9, result.returncode)
        self.assertIn("No .NET SDKs were found.", result.stdout)
        self.assertIn("Install a .NET SDK", result.stdout)
        self.assertNotIn("\ninformation: finishing\n", result.stdout)
        self.assertEqual("\n".join(lines) + "\n", raw)

    def test_noisy_success_emits_only_final_summary(self):
        result, raw = self.run_child("for i in range(2000): print('information: file', i)")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(1, len(result.stdout.splitlines()), result.stdout)
        self.assertIn("information=2000", result.stdout)
        self.assertEqual(2000, len(raw.splitlines()))

    def test_carriage_return_progress_is_visible_in_summary(self):
        result, raw = self.run_child("import sys; sys.stderr.write('Building [1/3]\\rBuilding [2/3]\\rBuilding [3/3]')")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(1, len(result.stdout.splitlines()), result.stdout)
        self.assertIn("3/3", result.stdout)
        self.assertIn("information=3", result.stdout)

    def test_invalid_interval_fails_before_launch(self):
        for value in ("0", "-1", "nan", "inf", "invalid"):
            with self.subTest(value=value):
                result, raw = self.run_child("print('launched')", CI_LOG_INTERVAL_SECONDS=value)
                self.assertEqual(2, result.returncode)
                self.assertNotIn("launched", raw)
                self.assertIn("CI_LOG_INTERVAL_SECONDS", result.stderr)

    def test_idle_heartbeat_and_signal_forwarding_with_live_child(self):
        with tempfile.TemporaryDirectory() as directory:
            code = ("import signal,sys; signal.signal(signal.SIGTERM, lambda *_: sys.exit(23)); "
                    "print('warning: child ready'); sys.stdin.readline()")
            child = subprocess.Popen([sys.executable, "-B", str(ROOT / "tools/scripts/ci_output.py"),
                "--stage", "current", "--log", str(pathlib.Path(directory) / "raw.log"), "--",
                sys.executable, "-u", "-c", code], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, env={**os.environ, "CI_LOG_INTERVAL_SECONDS": "0.05"})
            try:
                output = b""
                while b"status=running" not in output or b"warning: child ready" not in output:
                    ready, _, _ = select.select([child.stdout], [], [], 5)
                    self.assertTrue(ready, output)
                    chunk = os.read(child.stdout.fileno(), 65536)
                    self.assertTrue(chunk, output)
                    output += chunk
                self.assertIn(b"warning: child ready", output)
                self.assertIsNone(child.poll())
                child.send_signal(signal.SIGTERM)
                child.wait(timeout=5)
                rest, error = child.communicate(timeout=5)
                self.assertEqual(23, child.returncode, error)
                self.assertIn(b"exit=23", rest)
            finally:
                if child.poll() is None:
                    child.kill()
                child.communicate()

    def test_group_cancellation_reaches_shell_workload(self):
        with tempfile.TemporaryDirectory() as directory:
            child = subprocess.Popen([sys.executable, "-B", str(ROOT / "tools/scripts/ci_output.py"),
                "--stage", "current", "--log", str(pathlib.Path(directory) / "raw.log"), "--",
                "/bin/bash", "-c", 'trap "exit 2" TERM; "$1" -u -c "$2"', "fixture", sys.executable,
                "import sys; print('warning: workload ready'); sys.stdin.readline()"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            try:
                ready, _, _ = select.select([child.stdout], [], [], 5)
                self.assertTrue(ready)
                self.assertIn(b"workload ready", os.read(child.stdout.fileno(), 65536))
                os.killpg(child.pid, signal.SIGTERM)
                child.wait(timeout=5)
                output, error = child.communicate()
                self.assertEqual(2, child.returncode, output + error)
            finally:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.communicate()


class ResultSummaryTests(unittest.TestCase):
    def test_stage_summary_is_compact_and_preserves_failure_details(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "build/ci").mkdir(parents=True)
            value = {"stage": "current", "status": "failed", "exit": 2, "error": "missing report",
                     "scope": {"paths": [f"D5/LongPath{i}.lean" for i in range(1000)]},
                     "steps": [{"name": "lean-report", "status": "failed", "raw_exit": 17, "log": "build/ci/logs/current/lean-report.log"}]}
            (root / "build/ci/current-result.json").write_text(json.dumps(value))
            summary = root / "summary.md"
            result = subprocess.run([sys.executable, "-B", str(ROOT / "tools/scripts/workflow/ci.py"),
                                     "summary", "--repository", str(root), "--stage", "current"],
                                    env={**os.environ, "GITHUB_STEP_SUMMARY": str(summary)},
                                    capture_output=True, text=True, timeout=30)
            self.assertEqual(0, result.returncode, result.stderr)
            for text in (result.stdout, summary.read_text()):
                self.assertIn("missing report", text)
                self.assertIn("lean-report", text)
                self.assertIn("17", text)
                self.assertNotIn("LongPath", text)
            self.assertEqual(value, json.loads((root / "build/ci/current-result.json").read_text()))


if __name__ == "__main__":
    unittest.main()
