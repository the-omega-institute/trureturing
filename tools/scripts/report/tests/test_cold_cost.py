"""Behavior tests for the temporary observer; no workflow assertions."""
import importlib.util
import json
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

PROGRAM = Path(__file__).resolve().parents[1] / "cold_cost.py"
SPEC = importlib.util.spec_from_file_location("cold_cost", PROGRAM)
cost = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cost)


class SignalDiagnosticContractTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="signal contract ")
        self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name)

    def test_known_sender_individual_and_group_are_isolated_and_waited(self):
        fixture = cost.known_sender_fixture(self.output)
        self.assertEqual({r["mode"] for r in fixture}, {"individual", "group"})
        for row in fixture:
            self.assertNotEqual(row["pgid"], os.getpgrp())
            self.assertEqual(row["signal"], signal.SIGTERM)
            self.assertEqual(row["sender_returncode"], 0)
            self.assertTrue(all(v == -signal.SIGTERM for v in row["target_returncodes"]))
            self.assertEqual(len(row["targets"]), 1 if row["mode"] == "individual" else 2)

    def test_wire_event_identifies_sender_target_and_signed_group_request(self):
        line = "D\tsignal\t100\t15\t0\t0\t1\t0\t20\t20\t1\t20\t20\t90\tbash\t21\t21\t20\t21\t21\t91\tpython\n"
        event = cost.parse_signal_wire(line)
        self.assertEqual(event["sender"]["tgid"], 20)
        self.assertEqual(event["target"]["start_ns"], 91)
        self.assertEqual(event["group"], 1)
        call = cost.parse_signal_wire("D\tkill\t101\t15\t-21\t0\t0\t20\t20\t1\t20\t20\t90\tbash\n")
        self.assertEqual(call["requested_target"], -21)

    def test_ambiguous_sender_loss_and_missing_capability_prevent_report(self):
        for health in ({"ready": False}, {"ready": True, "lost_events": 1},
                       {"ready": True, "dropped_events": 2},
                       {"ready": True, "parse_errors": 1}):
            with self.subTest(health=health), self.assertRaises(ValueError):
                cost.require_trace_health(health)
        cost.require_trace_health({"ready": True, "lost_events": 0,
                                   "dropped_events": 0, "parse_errors": 0,
                                   "reader_error": None, "collector_returncode": None})
        event = cost.parse_signal_wire("D\tsignal\t100\t15\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\tunknown\t21\t21\t20\t21\t21\t91\tpython\n")
        with self.assertRaises(ValueError):
            cost.validate_fixture_attribution([event], [{"mode": "individual", "sender": {"pid": 20, "tgid": 20}, "targets": [{"pid": 21, "tgid":21}]}])

    def test_trace_retention_is_bounded_flushed_and_counts_drops(self):
        import io
        console = io.StringIO()
        sink = cost.SignalSink(self.output / "trace.jsonl", console=console, limit=2048)
        for _ in range(100):
            sink.emit({"kind": "signal", "sender": {"pid": 10}, "target": {"pid": 11}})
        sink.finish({"lost_events": 3})
        self.assertLessEqual((self.output / "trace.jsonl").stat().st_size, 2048)
        self.assertGreater(sink.dropped_events, 0)
        self.assertIn('"lost_events": 3', console.getvalue())
        self.assertIn('"retention": "censored"', console.getvalue())

    def test_absent_linux_bpf_capability_has_no_workload_side_effect(self):
        with patch.object(cost.platform, "system", return_value="Darwin"), \
                patch.object(cost.subprocess, "Popen") as launch:
            with self.assertRaises(ValueError):
                cost.SignalTrace(self.output).start()
            launch.assert_not_called()

    def test_exact_fixture_attribution_rejects_pid_reuse_and_missing_delivery(self):
        ident = lambda pid, birth: {"pid": pid, "tgid": pid, "ppid": 1, "pgid": 40,
                                    "sid": 1, "start_ns": birth, "comm": "python"}
        sender, target = ident(20, 1000000000), ident(21, 2000000000)
        fixtures = [{"mode": "individual", "pgid": 40, "sender": sender,
                     "targets": [dict(target, start_ticks=2 * os.sysconf("SC_CLK_TCK"))]}]
        events = [{"kind": "kill", "signal": 15, "requested_target": 21, "sender": sender},
                  {"kind": "signal", "signal": 15, "group": 1, "result": 0,
                   "sender": sender, "target": target},
                  {"kind": "delivery", "signal": 15, "target": target},
                  {"kind": "exit", "kernel_exit_code": 15, "actor": target}]
        cost.validate_fixture_attribution(events, fixtures)
        with self.assertRaisesRegex(ValueError, "delivery"):
            cost.validate_fixture_attribution([e for e in events if e["kind"] != "delivery"], fixtures)
        reused = [dict(e, target=dict(target, start_ns=3000000000)) if e["kind"] == "signal" else e for e in events]
        with self.assertRaises(ValueError):
            cost.validate_fixture_attribution(reused, fixtures)

    def test_kernel_oom_pid_schema_does_not_invent_victim_start_identity(self):
        event = cost.parse_signal_wire("D\toom-victim\t100\t77\t20\t20\t1\t20\t20\t90\tkworker\n")
        self.assertEqual(event["victim_pid"], 77)
        self.assertNotIn("target", event)
        self.assertIn("corroborating", event["victim_identity_limit"])

    def test_reader_reports_loss_schema_errors_and_never_echoes_private_text(self):
        import io
        trace = cost.SignalTrace(self.output)
        console = io.StringIO()
        trace.sink = cost.SignalSink(self.output / "wire.jsonl", console=console)
        trace._line("Lost 7 events")
        trace._line("ERROR private-token=signed-secret-url")
        self.assertEqual(trace.health["lost_events"], 7)
        self.assertEqual(trace.health["parse_errors"], 1)
        self.assertNotIn("signed-secret", console.getvalue())
        self.assertIn("compiler-or-attach", console.getvalue())
        trace.sink.finish(trace.health)

    def test_native_preflight_failure_executes_no_canonical_program(self):
        trace = Mock(sink=Mock(), stop=Mock(return_value={"ready": True, "lost_events": 0, "dropped_events": 0, "parse_errors": 0, "reader_error": None, "collector_returncode": 0}))
        trace.start.return_value = trace
        for mode in ("preflight", "workload"):
            with self.subTest(mode=mode), \
                    patch.object(cost, "native_binding", return_value={"inputs": {}}), \
                    patch.object(cost, "input_binding", return_value={}), \
                    patch.object(cost, "SignalTrace", return_value=trace), \
                    patch.object(cost, "emit_process_catalog"), \
                    patch.object(cost, "capability_preflight", side_effect=ValueError("capability absent")), \
                    patch.object(cost, "observe_command") as observe, \
                    patch.object(cost.subprocess, "check_output") as canonical:
                output = self.output / mode
                with self.assertRaises(ValueError):
                    cost.run(self.output, output, mode)
                observe.assert_not_called()
                canonical.assert_not_called()
                result = json.loads((output / "result.json").read_text())
                self.assertIsNone(result["canonical_returncode"])
                self.assertFalse(result["canonical_chain_complete"])

    def test_capability_only_success_does_not_execute_report_or_compiler(self):
        trace = Mock(sink=Mock(), stop=Mock(return_value={"ready": True, "lost_events": 0, "dropped_events": 0, "parse_errors": 0, "reader_error": None, "collector_returncode": 0}))
        trace.start.return_value = trace
        output = self.output / "capability-only"
        with patch.object(cost, "native_binding", return_value={"inputs": {}}), \
                patch.object(cost, "input_binding", return_value={}), \
                patch.object(cost, "SignalTrace", return_value=trace), \
                patch.object(cost, "emit_process_catalog"), \
                patch.object(cost, "capability_preflight", return_value={"status": "passed"}), \
                patch.object(cost, "observe_command") as observe, \
                patch.object(cost.subprocess, "check_output") as canonical:
            self.assertEqual(cost.run(self.output, output, "preflight"), 0)
            observe.assert_not_called()
            canonical.assert_not_called()
        result = json.loads((output / "result.json").read_text())
        self.assertFalse(result["canonical_chain_complete"])
        self.assertEqual(result["preflight"]["status"], "passed")

    def test_stage_identity_stream_excludes_arguments_and_keeps_raw_command_log(self):
        import io
        sink = cost.SignalSink(self.output / "stages-live.jsonl", console=io.StringIO())
        with patch.object(cost, "sample", return_value={"processes": [{"pid": 44, "ppid": 1,
                "pgid": 44, "sid": 1, "start_ticks": 55, "comm": "python", "role": "command-root"}]}):
            rc = cost.observe_command([sys.executable, "-c", 'import time; print("raw phase"); time.sleep(.02)', "private-argument"],
                    self.output, self.output, "identity", dict(os.environ), interval=.01, signal_sink=sink)
        sink.finish({})
        self.assertEqual(rc, 0)
        self.assertNotIn("private-argument", (self.output / "stages-live.jsonl").read_text())
        self.assertNotIn("private-argument", (self.output / "stages.jsonl").read_text())
        self.assertEqual((self.output / "identity.stdout.log").read_text(), "raw phase\n")


class ColdCostTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.output = self.root / "observations"
        self.output.mkdir()

    def compiler(self, body, arguments=None):
        fake = self.root / "fake-lean"
        fake.write_text("#!" + sys.executable + "\n" + body)
        fake.chmod(0o755)
        source = self.root / "Sample.lean"
        source.write_text("theorem sample : True := True.intro\n")
        setup = self.root / "setup.json"
        setup.write_text('{"name":"Sample","imports":[{"module":"Init"}]}')
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(fake))
        command = [sys.executable, str(PROGRAM), "compiler"] + (arguments or [str(source), "--setup", str(setup)])
        return subprocess.run(command, env=env, capture_output=True), source

    def test_compiler_preserves_outputs_status_arguments_and_setup(self):
        result, source = self.compiler('import sys\nprint("stdout")\nprint("checked fixture",file=sys.stderr)\nsys.exit(7)\n')
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout, b"stdout\n")
        self.assertEqual(result.stderr, b"checked fixture\n")
        folders = list((self.output / "compilers").iterdir())
        events = [json.loads(row) for row in (folders[0] / "events.jsonl").read_text().splitlines()]
        self.assertTrue(events[0]["profile_enabled"])
        self.assertNotIn("actual_argv", events[0])
        self.assertNotIn("original_argv", events[0])
        self.assertEqual(events[0]["sources"][0]["sha256"], cost.sha(source))
        self.assertEqual(events[1]["returncode"], 7)
        self.assertGreater(events[1]["monotonic_ns"], events[0]["monotonic_ns"])
        self.assertGreater(events[1]["maxrss"], 0)
        self.assertEqual((folders[0] / "setup.json").read_text(), (self.root / "setup.json").read_text())
        self.assertEqual((folders[0] / "stdout.log").read_bytes(), result.stdout)
        self.assertEqual((folders[0] / "stderr.log").read_bytes(), result.stderr)

    def test_compiler_preserves_signal_failure(self):
        for sig in (signal.SIGTERM, signal.SIGKILL):
            with self.subTest(signal=sig):
                before = set((self.output / "compilers").glob("*/events.jsonl"))
                result, _ = self.compiler(f'import os\nos.kill(os.getpid(),{int(sig)})\n')
                self.assertEqual(result.returncode, -sig, result.stderr.decode())
                events, = set((self.output / "compilers").glob("*/events.jsonl")) - before
                end = json.loads(events.read_text().splitlines()[-1])
                self.assertEqual(end["returncode"], -sig)
                self.assertEqual(os.waitstatus_to_exitcode(end["wait_status"]), -sig)
                self.assertGreater(end["maxrss"], 0)
                self.assertFalse((events.parent / "observer-errors.json").exists())

    def test_forwarding_keeps_waitable_child_status_owned_by_wait4(self):
        source = self.root / "Ready.lean"
        source.write_text("example : True := True.intro\n")
        child = Mock(pid=12345, returncode=None)
        child.stdout = tempfile.TemporaryFile()
        child.stderr = tempfile.TemporaryFile()
        handlers = {}

        def competing_reap(_sig):
            child.returncode = 7

        child.send_signal.side_effect = competing_reap

        def terminal_wait(pid, flags):
            self.assertEqual((pid, flags), (child.pid, 0))
            # A termination handler runs while the already-exited child is
            # waitable, before wait4 has consumed its status and accounting.
            handlers[signal.SIGTERM](signal.SIGTERM, None)
            if child.returncode is not None:
                raise ChildProcessError("forwarding consumed the terminal status")
            usage = Mock(ru_utime=.25, ru_stime=.125, ru_maxrss=4096,
                         ru_minflt=10, ru_majflt=0, ru_nvcsw=2, ru_nivcsw=1)
            return pid, 7 << 8, usage

        with patch.dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN="/fixture/lean"), \
                patch.object(cost.subprocess, "Popen", return_value=child), \
                patch.object(cost.signal, "signal", side_effect=lambda sig, fn: handlers.update({sig: fn})), \
                patch.object(cost.os, "kill") as kill, patch.object(cost.os, "wait4", side_effect=terminal_wait):
            self.assertEqual(cost.compiler([str(source)]), 7)
        kill.assert_called_once_with(child.pid, signal.SIGTERM)
        child.send_signal.assert_not_called()
        end = json.loads(next((self.output / "compilers").glob("*/events.jsonl")).read_text().splitlines()[-1])
        self.assertEqual(end["returncode"], 7)
        self.assertEqual(end["wait_status"], 7 << 8)
        self.assertEqual(end["user_cpu_seconds"], .25)
        self.assertEqual(end["received_signals"], [signal.SIGTERM])

    def test_live_forwarded_termination_preserves_signal_and_accounting(self):
        fake = self.root / "waiting-lean"
        fake.write_text("#!" + sys.executable + '\nimport time\nprint("ready", flush=True)\ntime.sleep(30)\n')
        fake.chmod(0o755)
        source = self.root / "Waiting.lean"
        source.write_text("example : True := True.intro\n")
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(fake))
        child = subprocess.Popen([sys.executable, str(PROGRAM), "compiler", str(source)], env=env,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            self.assertTrue(select.select([child.stdout], [], [], 10)[0], "compiler did not become ready")
            self.assertEqual(child.stdout.readline(), b"ready\n")
            child.send_signal(signal.SIGTERM)
            stdout, stderr = child.communicate(timeout=10)
            self.assertEqual(child.returncode, -signal.SIGTERM, stderr.decode())
            self.assertEqual(stdout, b"")
            self.assertEqual(stderr, b"")
            events = next((self.output / "compilers").glob("*/events.jsonl"))
            end = json.loads(events.read_text().splitlines()[-1])
            self.assertEqual(end["received_signals"], [signal.SIGTERM])
            self.assertEqual(end["returncode"], -signal.SIGTERM)
            self.assertEqual(os.waitstatus_to_exitcode(end["wait_status"]), -signal.SIGTERM)
            self.assertGreater(end["maxrss"], 0)
            self.assertEqual((events.parent / "stdout.log").read_bytes(), b"ready\n")
        finally:
            if child.poll() is None:
                child.kill()
            child.communicate(timeout=35)

    def test_noncompile_query_executes_without_profiler(self):
        result, _ = self.compiler('import sys\nprint(sys.argv[1:])\n', ["--version"])
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"['--version']\n")
        self.assertFalse((self.output / "compilers").exists())

    def test_stage_failure_keeps_raw_logs_even_when_sampler_unavailable(self):
        with patch.object(cost, "sample", side_effect=OSError("sample unavailable")):
            rc = cost.observe_command([sys.executable, "-c", 'import sys,time; print("raw"); print("err",file=sys.stderr); time.sleep(.05); sys.exit(9)'],
                                      self.root, self.output, "fixture", dict(os.environ), interval=.01)
        self.assertEqual(rc, 9)
        self.assertEqual((self.output / "fixture.stdout.log").read_text(), "raw\n")
        self.assertEqual((self.output / "fixture.stderr.log").read_text(), "err\n")
        end = json.loads((self.output / "stages.jsonl").read_text().splitlines()[-1])
        self.assertEqual(end["returncode"], 9)
        self.assertTrue((self.output / "observer-errors.jsonl").is_file())

    def test_linux_sample_types_scopes_and_descendant_selection(self):
        proc = self.root / "proc"
        proc.mkdir()
        for pid, parent, argv in (
                (10, 1, ["bash", "-c", "canonical resource wrapper"]),
                (11, 10, [sys.executable, str(PROGRAM), "compiler", "Sample.lean"]),
                (12, 11, ["/fixture/lean", "--profile", "Sample.lean"]),
                (13, 1, ["unrelated"]),
                (14, 10, ["bash", "-c", "canonical resource wrapper"])):
            folder = proc / str(pid)
            folder.mkdir()
            fields = ["S", str(parent)] + ["0"] * 22
            fields[11], fields[12], fields[19], fields[21] = "123", "456", "900", "42"
            (folder / "stat").write_text(f"{pid} (a tricky ) name) " + " ".join(fields))
            (folder / "cmdline").write_bytes(("\0".join(argv) + "\0").encode())
            (folder / "cgroup").write_text("0::/job\n")
        cg = self.root / "cgroup" / "job"
        cg.mkdir(parents=True)
        (cg / "cpu.stat").write_text("usage_usec 1234\n")
        (cg / "memory.events").write_text("oom_kill 2\n")
        row = cost.sample(10, proc, self.root / "cgroup", real_lean="/fixture/lean")
        self.assertEqual([p["pid"] for p in row["processes"]], [10, 11, 12, 14])
        self.assertEqual([p["role"] for p in row["processes"]],
                         ["command-root", "compiler-observer-wrapper", "real-compiler", "unclassified-command-descendant"])
        self.assertEqual(row["python_sampler"]["pid"], os.getpid())
        self.assertFalse(row["python_sampler"]["in_processes"])
        self.assertIn("includes compiler observer wrappers", row["scope"])
        self.assertIn("canonical shell sampler", row["scope"])
        self.assertIn("observer", row["cgroup_scope"])
        self.assertIn("observer", row["kernel_scope"])
        self.assertEqual(row["processes"][0]["start_ticks"], 900)
        self.assertEqual(row["processes"][0]["user_ticks"], 123)
        self.assertEqual(row["cgroup"]["cpu.stat"], "usage_usec 1234\n")
        self.assertEqual(row["cgroup"]["memory.events"], "oom_kill 2\n")
        self.assertIsNone(row["kernel"]["pressure/cpu"])
        self.assertIn("sampled", row["scope"])

    def run_fixture(self, stage_returns, producer_error=None, binding_error=None):
        output = self.root / "run-observations"
        real = (self.root / "lean").resolve()
        real.write_bytes(b"private compiler identity fixture")
        inputs = {"private-fixture": "unchanged"}
        trace = Mock(sink=Mock(), stop=Mock(return_value={"ready": True, "lost_events": 0, "dropped_events": 0, "parse_errors": 0, "reader_error": None, "collector_returncode": 0}))
        trace.start.return_value = trace

        def checked_output(command, **_kwargs):
            if command == ["elan", "which", "lean"]:
                return str(real).encode()
            if command == [str(real), "--version"]:
                return b"Lean (version 4.34.1)"
            if command == [str(real), "--githash"]:
                return b"fixture-githash"
            if command[1] == "tools/scripts/workflow/judge-lean-producer.sh":
                if producer_error:
                    raise producer_error
                return b"/fixture/producer.dll\n"
            raise AssertionError(command)

        with patch.object(cost, "native_binding", return_value={"inputs": inputs}), \
                patch.object(cost, "input_binding", side_effect=binding_error, return_value=inputs), \
                patch.object(cost, "SignalTrace", return_value=trace), \
                patch.object(cost, "emit_process_catalog"), \
                patch.object(cost, "capability_preflight", return_value={"status": "passed"}), \
                patch.object(cost.subprocess, "check_output", side_effect=checked_output), \
                patch.object(cost, "observe_command", side_effect=stage_returns) as observe:
            error = None
            rc = None
            try:
                rc = cost.run(self.root, output)
            except Exception as caught:
                error = caught
        return rc, error, json.loads((output / "result.json").read_text()), observe

    def test_producer_failure_receipt_keeps_raw_failure_and_incomplete_chain(self):
        failure = subprocess.CalledProcessError(17, ["private-producer"], output=b"failure")
        rc, error, result, observe = self.run_fixture([0], producer_error=failure)
        self.assertIsNone(rc)
        self.assertIs(error, failure)
        self.assertEqual(result["canonical_returncode"], 17)
        self.assertFalse(result["canonical_chain_complete"])
        self.assertEqual(result["canonical_failure"]["stage"], "judge-lean-producer")
        self.assertIsNone(result["observer_failure"])
        self.assertEqual(observe.call_count, 1)

    def test_observer_exception_receipt_has_unknown_canonical_result(self):
        failure = OSError("private observer launch failure")
        rc, error, result, observe = self.run_fixture([0, failure])
        self.assertIsNone(rc)
        self.assertIs(error, failure)
        self.assertIsNone(result["canonical_returncode"])
        self.assertFalse(result["canonical_chain_complete"])
        self.assertIsNone(result["canonical_failure"])
        self.assertEqual(result["observer_failure"]["stage"], "compiled-judge-test")
        self.assertEqual(observe.call_count, 2)

    def test_canonical_signal_failure_receipt_skips_later_stages(self):
        rc, error, result, observe = self.run_fixture([-signal.SIGKILL])
        self.assertIsNone(error)
        self.assertEqual(rc, 128 + signal.SIGKILL)
        self.assertEqual(result["canonical_returncode"], -signal.SIGKILL)
        self.assertFalse(result["canonical_chain_complete"])
        self.assertEqual(result["canonical_failure"]["stage"], "judge-build")
        self.assertIsNone(result["observer_failure"])
        self.assertEqual(observe.call_count, 1)

    def test_success_receipt_requires_complete_chain_and_preserved_inputs(self):
        rc, error, result, observe = self.run_fixture([0, 0, 0])
        self.assertIsNone(error)
        self.assertEqual(rc, 0)
        self.assertEqual(result["canonical_returncode"], 0)
        self.assertTrue(result["canonical_chain_complete"])
        self.assertTrue(result["inputs_unchanged"])
        self.assertIsNone(result["canonical_failure"])
        self.assertIsNone(result["observer_failure"])
        self.assertEqual(observe.call_count, 3)

    def test_full_report_uses_explicit_current_native_cache_policy(self):
        rc, error, result, observe = self.run_fixture([0, 0, 0])
        self.assertIsNone(error)
        self.assertEqual(rc, 0)
        self.assertTrue(result["canonical_chain_complete"])
        report_calls = [call for call in observe.call_args_list
                        if call.args[3] == "full-lean-report"]
        self.assertEqual(len(report_calls), 1)
        self.assertEqual(report_calls[0].args[0],
                         ["make", "lean-report", "LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build"])
        self.assertTrue(report_calls[0].kwargs["canonical_resources"])
        for call in observe.call_args_list:
            self.assertNotIn("LD_PRELOAD", call.args[4])
            self.assertNotIn("COLD_COST_REAL_LEAN", call.args[4])

    def test_final_input_observer_exception_does_not_leave_success_receipt(self):
        rc, error, result, _ = self.run_fixture([0, 0, 0], binding_error=OSError("private input read failure"))
        self.assertIsNone(rc)
        self.assertIsInstance(error, OSError)
        self.assertIsNone(result["canonical_returncode"])
        self.assertIsNone(result["inputs_unchanged"])
        self.assertEqual(result["observer_failure"]["stage"], "artifact-collection")

    def test_recorded_sampler_failure_fails_diagnostic_after_successful_commands(self):
        observe_command = cost.observe_command

        def observe(_command, cwd, output, name, _env, **_kwargs):
            # Exercise the existing sampler-error path with a real command;
            # canonical project commands remain private fixtures.
            with patch.object(cost, "sample", side_effect=OSError("private sample failure")):
                return observe_command([sys.executable, "-c", "import time; time.sleep(.05)"],
                                       cwd, output, name, dict(os.environ), interval=.01)

        rc, error, result, _ = self.run_fixture(observe)
        self.assertIsNone(rc)
        self.assertIsInstance(error, ValueError)
        self.assertIsNone(result["canonical_returncode"])
        self.assertTrue(result["canonical_chain_complete"])
        self.assertTrue(all(row["returncode"] == 0 for row in result["canonical_stages"]))
        self.assertIsNone(result["canonical_failure"])
        self.assertEqual(result["observer_failure"]["error"], "ValueError")

    def spawn_driver(self, linked=True):
        driver = self.root / "driver.c"
        driver.write_text('''#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
extern char **environ;
int main(int argc, char **argv) {
  if (argc < 2) return 2;
  char *kind = getenv("COLD_COST_TEST_SPAWN_KIND");
  if (kind && strcmp(kind,"execv")==0) { execv(argv[1],argv+1); return 2; }
  if (kind && strcmp(kind,"execvp")==0) { execvp(argv[1],argv+1); return 2; }
  if (kind && strcmp(kind,"execve")==0) { execve(argv[1],argv+1,environ); return 2; }
  pid_t pid; int status;
  int rc = kind && strcmp(kind,"posix_spawn")==0
    ? posix_spawn(&pid, argv[1], 0, 0, argv + 1, environ)
    : posix_spawnp(&pid, argv[1], 0, 0, argv + 1, environ);
  if (rc) return rc;
  if (waitpid(pid, &status, 0) < 0) return 2;
  return WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
}
''')
        executable = self.root / "driver"
        cmd = ["cc", "-Wall", "-Wextra", "-Werror", str(driver)]
        if linked:
            cmd += [str(PROGRAM.with_name("cold_cost_spawn.c"))]
        cmd += ["-o", str(executable)]
        if sys.platform == "linux":
            cmd += ["-ldl"]
        subprocess.run(cmd, check=True, capture_output=True)
        return executable

    def test_compiled_spawn_observer_forwards_and_does_not_recurse(self):
        driver = self.spawn_driver()
        lean = self.root / "lean"
        lean.write_text("#!" + sys.executable + '\nimport sys\nprint(sys.argv[1:])\nsys.exit(6)\n')
        lean.chmod(0o755)
        source = self.root / "Source.lean"
        source.write_text("example : True := True.intro\n")
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(lean),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        for kind in ("posix_spawn", "posix_spawnp", "execv", "execvp", "execve"):
            with self.subTest(kind=kind):
                result = subprocess.run([str(driver), str(lean), str(source)],
                                        env=dict(env, COLD_COST_TEST_SPAWN_KIND=kind), capture_output=True)
                self.assertEqual(result.returncode, 6)
                self.assertIn(b"--profile", result.stdout)
        self.assertEqual(len(list((self.output / "compilers").iterdir())), 5)
        query = subprocess.run([str(driver), str(lean), "--version"], env=env, capture_output=True)
        self.assertEqual(query.returncode, 6)
        self.assertNotIn(b"--profile", query.stdout)

    def test_native_entry_rejects_local_identity_before_any_execution(self):
        with patch.object(cost, "git", return_value=b"0" * 40), patch.dict(os.environ, {"GITHUB_EVENT_PATH": str(self.root / "event.json")}):
            (self.root / "event.json").write_text('{}')
            with self.assertRaisesRegex(ValueError, "genuine labeled"):
                cost.native_binding(self.root, dict(os.environ))

    def test_native_entry_accepts_publishable_label_only_for_exact_full_merge_sha(self):
        head = "0123456789abcdef0123456789abcdef01234567"
        base, pr_head, tree = "b" * 40, "c" * 40, "d" * 40
        event_path = self.root / "event.json"
        event = {"action": "labeled", "label": {"name": "cold-cost-" + head},
                 "pull_request": {"head": {"sha": pr_head}}}
        event_path.write_text(json.dumps(event))
        self.assertLessEqual(len(event["label"]["name"]), 50)
        env = {"GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "pull_request",
               "GITHUB_SHA": head, "GITHUB_EVENT_PATH": str(event_path)}
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        for relative in ("lake-manifest.json", "Reg/lake-manifest.json",
                         "tools/lean-inspector/lake-manifest.json", "tools/lean-inspector-interface/lake-manifest.json",
                         "tools/lean-inspector-reg/lake-manifest.json"):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"packages": [{"name": "mathlib",
                                                      "rev": "d13f23b723b8a846827a245b89c10fc7d3f11612"}]}))
        git_results = {("rev-parse", "HEAD"): head.encode(), ("show", "-s", "--format=%P", "HEAD"): f"{base} {pr_head}".encode(),
                       ("status", "--porcelain", "--untracked-files=all"): b"", ("rev-parse", "HEAD^{tree}"): tree.encode()}
        read_text = Path.read_text

        def fixture_text(path, *args, **kwargs):
            if path == Path("/etc/os-release"):
                return 'ID=ubuntu\nVERSION_ID="24.04"\n'
            return read_text(path, *args, **kwargs)

        with patch.object(cost, "git", side_effect=lambda root, *args: git_results[args]), \
                patch.object(cost, "production_binding", return_value={"H": cost.PRODUCTION_H}), \
                patch.object(cost, "input_binding", return_value={"git_blob_listing_sha256": cost.SEALED_INPUTS_SHA256}) as inputs, \
                patch.object(cost.platform, "system", return_value="Linux"), \
                patch.object(cost.platform, "machine", return_value="aarch64"), \
                patch.object(Path, "read_text", autospec=True, side_effect=fixture_text):
            binding = cost.native_binding(self.root, env)
            self.assertEqual((binding["head"], binding["protected_base"], binding["pr_head"]), (head, base, pr_head))
            inputs.assert_called_once_with(self.root)
            inputs.reset_mock()
            for label in ("cold-cost-" + head[:-1], "cold-cost-" + head[:-1] + "8", "cold-cost-reviewed-" + head):
                with self.subTest(label=label):
                    event["label"]["name"] = label
                    event_path.write_text(json.dumps(event))
                    with self.assertRaisesRegex(ValueError, "genuine labeled"):
                        cost.native_binding(self.root, env)
                    inputs.assert_not_called()

    @unittest.skipUnless(os.environ.get("COLD_COST_TEST_LEAN"), "requires explicitly supplied pinned test compiler")
    def test_actual_pinned_compiler_spawn_keeps_toolchain_and_olean_bytes(self):
        # Independent core fixture, not a repository build or report acceptance.
        real = Path(os.environ["COLD_COST_TEST_LEAN"]).resolve()
        source = self.root / "Fixture.lean"
        source.write_text("def diagnostic_fixture : Nat := 3\ntheorem diagnostic_fixture_ok : diagnostic_fixture = 3 := rfl\n")
        original = source.read_bytes()
        baseline = self.root / "control.olean"
        control = subprocess.run([str(real), "-Dprofiler.threshold=0", "-o", str(baseline), str(source)],
                                 cwd=self.root, capture_output=True)
        self.assertEqual(control.returncode, 0, control.stderr.decode())
        driver = self.spawn_driver()
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(real),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        observed = self.root / "observed.olean"
        result = subprocess.run([str(driver), str(real), "-Dprofiler.threshold=0", "-o", str(observed), str(source)],
                                cwd=self.root, env=env, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"type checking", result.stderr)
        self.assertEqual(source.read_bytes(), original)
        self.assertEqual(cost.sha(baseline), cost.sha(observed))
        events = next((self.output / "compilers").glob("*/events.jsonl"))
        self.assertTrue(json.loads(events.read_text().splitlines()[0])["profile_enabled"])
        self.assertEqual(cost.sha(real), cost.sha(Path(os.environ["COLD_COST_TEST_LEAN"])))

    @unittest.skipUnless(sys.platform == "linux", "actual LD_PRELOAD requires Linux")
    def test_linux_dynamic_spawn_observer(self):
        library = cost.build_spawn_observer(self.output)
        driver = self.spawn_driver(linked=False)
        lean = self.root / "lean"
        lean.write_text("#!" + sys.executable + '\nimport sys\nprint(sys.argv[1:])\nsys.exit(4)\n')
        lean.chmod(0o755)
        source = self.root / "Source.lean"
        source.write_text("example : True := True.intro\n")
        env = dict(os.environ, LD_PRELOAD=str(library), COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(lean),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        result = subprocess.run([str(driver), str(lean), str(source)], env=env, capture_output=True)
        self.assertEqual(result.returncode, 4)
        self.assertIn(b"--profile", result.stdout)
        self.assertEqual(len(list((self.output / "compilers").iterdir())), 1)


if __name__ == "__main__":
    unittest.main()
