"""Behavior tests for the temporary observer; no workflow assertions."""
import importlib.util
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

PROGRAM = Path(__file__).resolve().parents[1] / "cold_cost.py"
SPEC = importlib.util.spec_from_file_location("cold_cost", PROGRAM)
cost = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cost)

HEALTHY = {"ready": True, "lost_events": 0, "dropped_events": 0, "parse_errors": 0,
           "reader_error": None, "collector_returncode": None}


class PortableOwnedCommand:
    """Test double for control flow on Darwin, NOT Linux ownership evidence.

    Existing portable fixtures use cooperative parents that wait their leaves.
    Orphan adoption is exercised only by LinuxOwnershipTests without this double.
    """
    def __init__(self, command, **kwargs):
        self.process = subprocess.Popen(command, process_group=0, **kwargs)
        self.pid = self.process.pid
        self.returncode = None
        self.cleanup = None

    def poll(self):
        self.returncode = self.process.poll()
        if self.returncode is not None:
            self.cleanup = {"root_reaped": True, "workload_reaped": True,
                            "fixture_scope": "portable cooperative direct group only"}
        return self.returncode

    def stop(self):
        try:
            os.killpg(self.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        try:
            os.killpg(self.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        self.process.wait(timeout=2)
        self.poll()
        return self.cleanup

    def close(self):
        pass


def portable_control_flow(test):
    if sys.platform != "linux":
        patcher = patch.object(cost, "OwnedCommand", PortableOwnedCommand)
        patcher.start()
        test.addCleanup(patcher.stop)


class ProviderStartupTests(unittest.TestCase):
    """Portable launch/stdio fixtures; no hosted ARM or privilege evidence."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="provider startup ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.calls = self.root / "calls.jsonl"
        provider = self.root / "provider"
        (provider / "bin").mkdir(parents=True)
        (provider / "squashfs-root").mkdir()
        self.driver = self.root / "provider.py"
        self.driver.write_text(f'''import json,os,signal,sys,time
with open({str(self.calls)!r}, "a") as stream:
    stream.write(json.dumps({{"args":sys.argv[1:],"env":dict(os.environ)}})+"\\n")
if sys.argv[1:] == ["--version"]:
    os.write(1,b"bpftrace v0.27.0\\n")
    sys.exit(0)
signal.signal(signal.SIGINT,lambda *_: sys.exit(0))
os.write(1,b"D\\tready\\n")
time.sleep(30)
''')
        import shlex
        apprun = provider / "squashfs-root" / "AppRun"
        apprun.write_text(f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -B {shlex.quote(str(self.driver))} \"$@\"\n")
        apprun.chmod(0o755)
        self.tool = provider / "bin" / "bpftrace"
        self.tool.symlink_to("../squashfs-root/AppRun")
        sudo = provider / "bin" / "sudo"
        sudo.write_text('#!/bin/sh\n[ "$1" = -n ] || exit 23\nshift\nexec "$@"\n')
        sudo.chmod(0o755)
        self.env = dict(os.environ, PATH=str(provider / "bin") + os.pathsep + os.environ["PATH"])

    def records(self, output):
        return [json.loads(line) for line in (output / "signal-trace.jsonl").read_text().splitlines()]

    def test_both_consumers_use_same_privileged_launcher_and_keep_arguments_and_environment(self):
        real_popen = subprocess.Popen
        for uid in (0, 1001):
            with self.subTest(uid=uid):
                output = self.root / str(uid)
                output.mkdir()
                trace = cost.SignalTrace(output, seconds=90)
                launches = []
                def launch(command, **kwargs):
                    launches.append((command, kwargs))
                    return real_popen(command, **kwargs)
                with patch.dict(os.environ, self.env, clear=True), \
                        patch.object(cost.platform, "system", return_value="Linux"), \
                        patch.object(cost.Path, "is_file", return_value=True), \
                        patch.object(cost.os, "geteuid", return_value=uid), \
                        patch.object(cost.sys, "stdout", io.StringIO()), \
                        patch.object(cost.subprocess, "Popen", side_effect=launch):
                    try:
                        trace.start()
                        self.assertTrue(trace.health["ready"])
                    finally:
                        trace.stop()
                        if trace.process:
                            trace.process.stdout.close()
                            trace.process.stderr.close()
                prefix = [] if uid == 0 else ["sudo", "-n"]
                self.assertEqual([row[0] for row in launches], [
                    prefix + [str(self.tool), "--version"],
                    prefix + [str(self.tool), "-q", "-B", "line", "-e", cost.signal_program(90)]])
                self.assertEqual(launches[1][1]["env"],
                                 {"PATH": self.env["PATH"], "BPFTRACE_PERF_RB_PAGES": "64"})
                records = self.records(output)
                version = next(row for row in records if row["kind"] == "provider-version")
                self.assertEqual(version["returncode"], 0)
                self.assertEqual(base64.b64decode(version["stdout"]["raw_bytes_base64"]), b"bpftrace v0.27.0\n")
                self.assertEqual(version["stderr"]["raw_byte_length"], 0)
                self.assertEqual(records[-1]["collector_returncode"], 0)
                self.assertEqual(records[-1]["parse_errors"], 0)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()]
        self.assertEqual(len(calls), 4)
        for call in calls[1::2]:
            self.assertEqual(call["args"], ["-q", "-B", "line", "-e", cost.signal_program(90)])
            self.assertEqual(call["env"]["BPFTRACE_PERF_RB_PAGES"], "64")

    def test_version_127_retains_original_binary_stdio_and_stops_before_collector(self):
        self.driver.write_text("import os,sys\nos.write(1,b'version-out\\xff')\nos.write(2,b'launcher-error\\xfe\\n')\nsys.exit(127)\n")
        trace = cost.SignalTrace(self.root)
        with patch.dict(os.environ, self.env, clear=True), \
                patch.object(cost.platform, "system", return_value="Linux"), \
                patch.object(cost.Path, "is_file", return_value=True), \
                patch.object(cost.os, "geteuid", return_value=1001), \
                patch.object(cost.sys, "stdout", io.StringIO()):
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                trace.start()
        self.assertEqual(caught.exception.returncode, 127)
        self.assertIsNone(trace.process)
        rows = self.records(self.root)
        version = next(row for row in rows if row["kind"] == "provider-version")
        self.assertEqual(version["command"], ["sudo", "-n", str(self.tool), "--version"])
        self.assertEqual(version["returncode"], 127)
        for name, raw in (("stdout", b"version-out\xff"), ("stderr", b"launcher-error\xfe\n")):
            self.assertEqual(base64.b64decode(version[name]["raw_bytes_base64"]), raw)
            self.assertEqual(version[name]["raw_sha256"], hashlib.sha256(raw).hexdigest())
        self.assertFalse(rows[-1]["ready"])

    def test_version_timeout_and_launch_error_keep_unknown_status_and_partial_bytes(self):
        for error in (subprocess.TimeoutExpired(["provider", "--version"], 5,
                                               output=b"partial\xff", stderr=b"failure\xfe"),
                      FileNotFoundError(2, "private fixture missing")):
            with self.subTest(error=type(error).__name__):
                trace = cost.SignalTrace(self.root)
                trace.sink = cost.SignalSink(self.root / "signal-trace.jsonl", console=io.StringIO())
                with patch.object(cost.subprocess, "run", side_effect=error):
                    with self.assertRaises(type(error)):
                        trace._provider_version(["provider", "--version"])
                trace.stop()
                version = self.records(self.root)[0]
                self.assertIsNone(version["returncode"])
                self.assertEqual(version["outcome"], "timeout" if isinstance(error, subprocess.TimeoutExpired) else "launch-error")
                if isinstance(error, subprocess.TimeoutExpired):
                    self.assertEqual(base64.b64decode(version["stderr"]["raw_bytes_base64"]), b"failure\xfe")
                else:
                    self.assertEqual(version["errno"], 2)

    def test_version_truncation_is_bounded_and_charged_as_evidence_loss(self):
        trace = cost.SignalTrace(self.root)
        trace.sink = cost.SignalSink(self.root / "signal-trace.jsonl", console=io.StringIO())
        raw = b"x" * (cost.COLLECTOR_DIAGNOSTIC_LIMIT + 1)
        trace._record_provider_version(["provider", "--version"], 127, raw, raw, "completed")
        trace.stop()
        rows = self.records(self.root)
        self.assertEqual(rows[-1]["dropped_events"], 2)
        self.assertEqual(rows[-1]["retention"], "censored")
        for name in ("stdout", "stderr"):
            self.assertTrue(rows[0][name]["truncated"])
            self.assertEqual(rows[0][name]["observed_byte_length"], len(raw))
            self.assertEqual(base64.b64decode(rows[0][name]["raw_bytes_base64"]), raw[:-1])


class SignalDiagnosticContractTests(unittest.TestCase):
    def setUp(self):
        portable_control_flow(self)
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
        self.assertEqual(event["boottime_ns"], 100)
        self.assertEqual(event["event_clock"], "CLOCK_BOOTTIME")
        self.assertNotIn("monotonic_ns", event)
        self.assertEqual(event["identity_start_clock"], "boot-nanoseconds")
        self.assertEqual(cost.stamp()["monotonic_clock"], "CLOCK_MONOTONIC")
        self.assertEqual(event["sender"]["tgid"], 20)
        self.assertEqual(event["target"]["start_ns"], 91)
        self.assertEqual(event["group"], 1)
        call = cost.parse_signal_wire("D\tkill\t101\t15\t-21\t0\t0\t20\t20\t1\t20\t20\t90\tbash\n")
        self.assertEqual(call["requested_target"], -21)

    def test_ambiguous_sender_loss_and_missing_capability_prevent_report(self):
        for key, value in (("ready", False), ("lost_events", 1), ("dropped_events", 2),
                           ("parse_errors", 1), ("reader_error", "OSError"), ("collector_returncode", 7)):
            health = dict(HEALTHY, **{key: value})
            with self.subTest(health=health), self.assertRaises(ValueError):
                cost.require_trace_health(health)
        cost.require_trace_health(HEALTHY)
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

    def test_reader_retains_loss_and_malformed_bytes_without_plaintext_console(self):
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
        records = [json.loads(line) for line in (self.output / "wire.jsonl").read_text().splitlines()]
        retained = [base64.b64decode(row["raw_bytes_base64"]) for row in records
                    if row["kind"] == "collector-diagnostic"]
        self.assertEqual(retained, [b"Lost 7 events", b"ERROR private-token=signed-secret-url"])

    def collect_failure(self, trace, body, console=None, limit=cost.TRACE_LIMIT):
        """Feed actual collector pipes to the report's reader/sink consumer."""
        trace.sink = cost.SignalSink(trace.output / "signal-trace.jsonl",
                                     console=io.StringIO() if console is None else console, limit=limit)
        child = subprocess.Popen([
            sys.executable, "-c",
            "import os,sys,resource; resource.setrlimit(resource.RLIMIT_CORE,(0,0)); " + body,
        ], stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=trace.output)
        trace.process = child
        self.addCleanup(child.stdout.close)
        self.addCleanup(child.stderr.close)
        self.addCleanup(trace.stop)
        trace.deadline = time.monotonic() + 5
        trace.thread = threading.Thread(target=trace._read)
        trace.thread.start()
        trace.thread.join(timeout=5)
        self.assertFalse(trace.thread.is_alive())
        child.wait(timeout=2)
        health = trace.stop()
        self.assertTrue(trace.sink.closed)
        self.assertIsNotNone(child.poll())
        with self.assertRaises(ValueError):
            cost.require_trace_health(health)
        records = [json.loads(line) for line in (trace.output / "signal-trace.jsonl").read_text().splitlines()]
        diagnostics = [row for row in records if row.get("kind") == "collector-diagnostic"]
        self.assertTrue(diagnostics)
        for row in diagnostics:
            raw = base64.b64decode(row["raw_bytes_base64"], validate=True)
            self.assertEqual(row["raw_byte_length"], len(raw))
            self.assertEqual(row["raw_line_sha256"], hashlib.sha256(raw).hexdigest())
            self.assertLessEqual(len(raw), 65536)
        self.assertEqual(records[-1]["kind"], "trace-terminal")
        self.assertEqual(records[-1]["collector_returncode"], child.returncode)
        return health, records, diagnostics

    def test_collector_failure_retains_stdout_stderr_and_eof_bytes_with_raw_status(self):
        # GoalArtifact report/integration evidence: both streams, byte identity,
        # EOF, wire-like stderr, raw abort status and cleanup use actual pipes.
        trace = cost.SignalTrace(self.output)
        health, records, diagnostics = self.collect_failure(trace,
            "os.write(1,b'collector\\xff\\nstdout-tail\\x80'); "
            "os.write(2,b'D\\tready\\nattach\\xfe\\nstderr-tail\\x00'); os.abort()")
        self.assertEqual(health["collector_returncode"], -signal.SIGABRT)
        self.assertFalse(health["ready"])
        self.assertFalse(any(row["kind"] == "trace-ready" for row in records))
        expected = {"stdout": b"collector\xff\nstdout-tail\x80",
                    "stderr": b"D\tready\nattach\xfe\nstderr-tail\x00"}
        for stream, original in expected.items():
            recovered = b"".join(base64.b64decode(row["raw_bytes_base64"]) +
                                  (b"\n" if row["terminated"] else b"")
                                  for row in diagnostics if row["stream"] == stream)
            self.assertEqual(recovered, original)
        self.assertTrue(all(not row["truncated"] for row in diagnostics))

    def test_actual_startup_failure_keeps_source_inventory_and_forbids_workload(self):
        # run's current publication consumer must bind recoverable failure
        # evidence while refusing GoalArtifact canonical work in either mode.
        inputs = {"private_fixture_program_sha256": cost.sha(PROGRAM)}
        binding = {"inputs": inputs, "head": "d36a2901ec0c24cc055c6f03bc7dcf55183340d7",
                   "fixture_scope": "local collector pipes; no native capability"}
        for mode in ("preflight", "workload"):
            with self.subTest(mode=mode):
                output = self.output / mode
                trace = cost.SignalTrace(output)
                def start():
                    self.collect_failure(trace, "os.write(2,b'attachment-failure\\xff'); os.abort()")
                    trace.check()
                trace.start = start
                with patch.object(cost, "native_binding", return_value=binding), \
                        patch.object(cost, "input_binding", return_value=inputs), \
                        patch.object(cost, "SignalTrace", return_value=trace), \
                        patch.object(cost, "capability_preflight") as preflight, \
                        patch.object(cost, "observe_command") as command, \
                        patch.object(cost, "observe_output") as query:
                    with self.assertRaises(cost.TraceHealthError):
                        cost.run(self.output, output, mode)
                preflight.assert_not_called()
                command.assert_not_called()
                query.assert_not_called()
                self.assertEqual(json.loads((output / "source.json").read_text()), binding)
                result = json.loads((output / "result.json").read_text())
                self.assertFalse(result["canonical_chain_complete"])
                self.assertEqual(result["canonical_stages"], [])
                self.assertIsNone(result["canonical_returncode"])
                self.assertTrue(result["inputs_unchanged"])
                self.assertEqual(result["observer_failure"]["retention"], "censored")
                self.assertEqual(result["observer_failure"]["trace_health"]["collector_returncode"], -signal.SIGABRT)
                inventory = json.loads((output / "inventory.json").read_text())
                self.assertTrue({"source.json", "result.json", "signal-trace.jsonl"} <= {r["path"] for r in inventory})
                for row in inventory:
                    artifact = output / row["path"]
                    self.assertEqual(row["sha256"], cost.sha(artifact))
                    self.assertEqual(row["bytes"], artifact.stat().st_size)

    def test_oversized_collector_output_is_censored_and_continuation_is_not_wire(self):
        # The reader's bounded fragment buffer serves require_trace_health;
        # truncation must be visible and cannot turn a suffix into readiness.
        for suffix in (b"\n", b"x" * 131072 + b"D\tready\n"):
            with self.subTest(suffix_bytes=len(suffix)):
                output = self.output / str(len(suffix))
                output.mkdir()
                trace = cost.SignalTrace(output)
                tail = "b'\\n'" if suffix == b"\n" else "b'x'*131072+b'D\\tready\\n'"
                health, records, diagnostics = self.collect_failure(
                    trace, "sys.stdout.buffer.write(b'collector-long-'+b'x'*65536+" + tail +
                           "); sys.stdout.buffer.flush(); sys.exit(23)",
                    limit=512 * 1024)
                self.assertEqual(health["collector_returncode"], 23)
                self.assertFalse(health["ready"])
                self.assertTrue(any(row["truncated"] for row in diagnostics))
                self.assertTrue(any(base64.b64decode(row["raw_bytes_base64"]).startswith(b"collector-long-")
                                    for row in diagnostics))
                self.assertEqual(records[-1]["retention"], "censored")

    def test_failure_diagnostics_obey_trace_live_byte_guard(self):
        # SignalSink's existing trace/live cap includes encoded diagnostics.
        trace = cost.SignalTrace(self.output)
        console = io.StringIO()
        health, records, diagnostics = self.collect_failure(
            trace, "sys.stdout.buffer.write(b'attach-failure-\\xff\\n'*100); sys.exit(19)",
            console=console, limit=2048)
        self.assertGreater(health["dropped_events"], 0)
        self.assertLessEqual(len(console.getvalue().encode()), 2048)
        self.assertLessEqual((self.output / "signal-trace.jsonl").stat().st_size, 2048)
        self.assertEqual(base64.b64decode(diagnostics[0]["raw_bytes_base64"]), b"attach-failure-\xff")
        self.assertEqual(records[-1]["retention"], "censored")

    def test_failure_diagnostics_under_live_backpressure_keep_bytes_and_cleanup(self):
        # The existing bounded live-delivery consumer must not trap the reader
        # or stop/finish when retaining the actual startup failure family.
        read_fd, write_fd = os.pipe()
        self.addCleanup(os.close, read_fd)
        console = os.fdopen(write_fd, "w", buffering=1)
        self.addCleanup(console.close)
        os.set_blocking(write_fd, False)
        try:
            while True:
                os.write(write_fd, b"x" * 4096)
        except BlockingIOError:
            pass
        os.set_blocking(write_fd, True)
        begin = time.monotonic()
        trace = cost.SignalTrace(self.output)
        health, records, diagnostics = self.collect_failure(
            trace, "os.write(2,b'loader-failure\\xfd\\n'); sys.exit(17)", console=console)
        self.assertLess(time.monotonic() - begin, 3)
        self.assertEqual(health["collector_returncode"], 17)
        self.assertEqual(health["console_error"], "TimeoutError")
        self.assertTrue(os.get_blocking(write_fd))
        self.assertEqual(base64.b64decode(diagnostics[0]["raw_bytes_base64"]), b"loader-failure\xfd")
        self.assertEqual(records[-1]["retention"], "censored")

    def read_budget_failure(self, trace, console, failure, stream="stdout", limit=24576):
        """Actual collector reader, descriptor delivery and failing retention."""
        trace.sink = cost.SignalSink(trace.output / "signal-trace.jsonl", console=console, limit=limit)
        retained = trace.sink.stream
        trace.sink.stream = Mock(wraps=retained)
        if failure:
            getattr(trace.sink.stream, failure).side_effect = OSError("fixture retention failure")
        child = subprocess.Popen([sys.executable, "-c", r'''
import os,signal,sys,time
signal.signal(signal.SIGINT, lambda *_: sys.exit(19))
os.write(1,b'D\tready\n')
fd=int(sys.argv[1])
for i in range(24):
    raw=b'collector-budget-'+str(i).encode()+b'-\xff'+b'x'*5000+b'\n'
    while raw:
        raw=raw[os.write(fd,raw):]
os.write(fd,b'collector-eof-\xfe')
os.close(1); os.close(2)
time.sleep(30)
''', "1" if stream == "stdout" else "2"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        trace.process = child
        self.addCleanup(child.stdout.close)
        self.addCleanup(child.stderr.close)
        self.addCleanup(trace.stop)
        trace.deadline = time.monotonic() + 5
        trace.thread = threading.Thread(target=trace._read)
        trace.thread.start()
        trace.thread.join(timeout=3)
        self.assertFalse(trace.thread.is_alive())
        self.assertIsNone(child.poll())
        self.assertTrue(trace.health["ready"])
        self.assertEqual(trace.health["parse_errors"], 25)

    def test_reader_live_budget_survives_repeated_write_and_flush_failure(self):
        # GoalArtifact fixed trace/live guard and workload refusal share the
        # actual reader/sink; a healthy fd exposes bytes despite local loss.
        inputs = {"private_fixture_program_sha256": cost.sha(PROGRAM)}
        binding = {"inputs": inputs, "fixture_scope": "portable collector pipes; no native capability"}
        for failure in ("write", "flush"):
            for stream in ("stdout", "stderr"):
                for mode in ("preflight", "workload"):
                    with self.subTest(failure=failure, stream=stream, mode=mode):
                        name = f"{failure}-{stream}-{mode}"
                        output = self.output / name
                        trace = cost.SignalTrace(output)
                        with (self.output / (name + ".live")).open("w+b", buffering=0) as console:
                            def start():
                                self.read_budget_failure(trace, console, failure, stream)
                                try:
                                    trace.check()
                                finally:
                                    trace.stop()
                            trace.start = start
                            with patch.object(cost, "native_binding", return_value=binding), \
                                    patch.object(cost, "input_binding", return_value=inputs), \
                                    patch.object(cost, "SignalTrace", return_value=trace), \
                                    patch.object(cost, "capability_preflight") as preflight, \
                                    patch.object(cost, "observe_command") as command, \
                                    patch.object(cost, "observe_output") as query:
                                with self.assertRaises(ValueError):
                                    cost.run(self.output, output, mode)
                            preflight.assert_not_called()
                            command.assert_not_called()
                            query.assert_not_called()
                            console.seek(0)
                            delivered = console.read()
                            print("FIXTURE_RESULT " + json.dumps({"consumer": "collector-reader/shared-sink",
                                  "failure": failure, "stream": stream, "mode": mode,
                                  "live_bytes": len(delivered), "limit": trace.sink.limit}), flush=True)
                            self.assertLessEqual(len(delivered), trace.sink.limit)
                            self.assertTrue(os.get_blocking(console.fileno()))
                        rows = [json.loads(line.removeprefix(b"SIGNAL_DIAGNOSTIC "))
                                for line in delivered.splitlines()]
                        diagnostics = [r for r in rows if r["kind"] == "collector-diagnostic"]
                        self.assertGreaterEqual(sum(r["terminated"] for r in diagnostics), 2)
                        for row in diagnostics:
                            raw = base64.b64decode(row["raw_bytes_base64"], validate=True)
                            if row["terminated"]:
                                self.assertTrue(raw.startswith(b"collector-budget-"))
                                self.assertGreater(len(raw), 4096)
                            else:
                                self.assertEqual(raw, b"collector-eof-\xfe")
                            self.assertEqual(row["stream"], stream)
                            self.assertEqual(row["raw_byte_length"], len(raw))
                            self.assertEqual(row["raw_line_sha256"], hashlib.sha256(raw).hexdigest())
                            self.assertFalse(row["truncated"])
                        self.assertEqual(rows[-1]["kind"], "trace-terminal")
                        self.assertEqual(rows[-1]["retention"], "censored")
                        self.assertEqual(rows[-1]["collector_returncode"], 19)
                        health = trace.snapshot()
                        self.assertEqual(health["retention_error"], "OSError")
                        self.assertIsNone(health["console_error"])
                        self.assertGreater(health["dropped_events"], 0)
                        with self.assertRaises(ValueError):
                            cost.require_trace_health(health)
                        self.assertTrue(trace.sink.closed)
                        with self.assertRaises(ProcessLookupError):
                            os.kill(trace.process.pid, 0)
                        self.assertLessEqual((output / "signal-trace.jsonl").stat().st_size, trace.sink.limit)
                        self.assertEqual(json.loads((output / "source.json").read_text()), binding)
                        result = json.loads((output / "result.json").read_text())
                        self.assertFalse(result["canonical_chain_complete"])
                        self.assertEqual(result["canonical_stages"], [])
                        self.assertIsNone(result["canonical_returncode"])
                        self.assertTrue(result["inputs_unchanged"])
                        self.assertEqual(result["observer_failure"]["retention"], "censored")
                        for row in json.loads((output / "inventory.json").read_text()):
                            artifact = output / row["path"]
                            self.assertEqual(row["sha256"], cost.sha(artifact))
                            self.assertEqual(row["bytes"], artifact.stat().st_size)

    def test_reader_retention_failure_terminal_exact_cap_and_one_byte_over(self):
        # Measure the actual terminal encoding, then exercise finish's boundary
        # with the same reader and persistent local failure, never a mirror.
        for failure in ("write", "flush"):
            terminal_size = None
            for delta in (None, 0, -1):
                with self.subTest(failure=failure, delta=delta):
                    output = self.output / f"terminal-{failure}-{delta}"
                    output.mkdir()
                    trace = cost.SignalTrace(output)
                    with (output / "live").open("w+b", buffering=0) as console:
                        self.read_budget_failure(trace, console, failure)
                        before = console.tell()
                        if delta is not None:
                            trace.sink.limit = before + terminal_size + delta
                        trace.stop()
                        console.seek(0)
                        delivered = console.read()
                    if delta is None:
                        terminal_size = len(delivered) - before
                    print("FIXTURE_RESULT " + json.dumps({"consumer": "collector-reader/trace-terminal",
                          "failure": failure, "boundary_delta": delta, "before_terminal": before,
                          "live_bytes": len(delivered), "limit": trace.sink.limit}), flush=True)
                    self.assertLessEqual(len(delivered), trace.sink.limit)
                    self.assertEqual(trace.process.returncode, 19)
                    self.assertTrue(trace.sink.closed)
                    if delta == -1:
                        self.assertEqual(len(delivered), before)
                    else:
                        terminal = delivered[before:]
                        row = json.loads(terminal.removeprefix(b"SIGNAL_DIAGNOSTIC "))
                        self.assertEqual(row["kind"], "trace-terminal")
                        self.assertEqual(row["retention"], "censored")
                        if delta is not None:
                            self.assertEqual(len(delivered), trace.sink.limit)

    def test_reader_partial_and_zero_live_delivery_with_retention_failure(self):
        # Partial delivery is measured at the descriptor, and a latched console
        # failure must remain bounded while the reader drains further records.
        real_write = os.write
        for failure in ("write", "flush"):
            for delivery in ("partial", "zero"):
                with self.subTest(failure=failure, delivery=delivery):
                    output = self.output / f"{failure}-{delivery}"
                    output.mkdir()
                    trace = cost.SignalTrace(output)
                    with (output / "live").open("w+b", buffering=0) as console:
                        calls = []
                        def write(fd, data):
                            if fd != console.fileno():
                                return real_write(fd, data)
                            calls.append(len(data))
                            if delivery == "zero":
                                return 0
                            if len(calls) == 1:
                                return real_write(fd, data[:31])
                            raise BrokenPipeError("fixture partial console failure")
                        with patch.object(cost.os, "write", side_effect=write):
                            self.read_budget_failure(trace, console, failure)
                            health = trace.stop()
                        console.seek(0)
                        delivered = console.read()
                        self.assertTrue(os.get_blocking(console.fileno()))
                    print("FIXTURE_RESULT " + json.dumps({"consumer": "collector-reader/shared-delivery",
                          "failure": failure, "delivery": delivery, "live_bytes": len(delivered),
                          "limit": trace.sink.limit}), flush=True)
                    self.assertEqual(len(delivered), 31 if delivery == "partial" else 0)
                    self.assertEqual(len(calls), 2 if delivery == "partial" else 1)
                    self.assertLessEqual(len(delivered), trace.sink.limit)
                    self.assertEqual(health["console_error"], "BrokenPipeError" if delivery == "partial" else "OSError")
                    self.assertEqual(health["retention_error"], "OSError")
                    self.assertEqual(health["collector_returncode"], 19)
                    self.assertTrue(trace.sink.closed)
                    self.assertLessEqual((output / "signal-trace.jsonl").stat().st_size, trace.sink.limit)
                    with self.assertRaises(ValueError):
                        cost.require_trace_health(health)

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


class LiveHealthEnforcementTests(unittest.TestCase):
    failures = ("loss", "parse", "reader", "collector-error", "collector-exit", "console", "file")

    def setUp(self):
        portable_control_flow(self)
        self.fresh_case()

    def fresh_case(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="live health ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.output = self.root / "output"
        self.real = self.root / "lean identity"
        self.real.write_bytes(b"compiler identity fixture")

    def trace(self, output):
        output.mkdir(exist_ok=True)
        trace = cost.SignalTrace(output)
        trace.health.update({k: v for k, v in HEALTHY.items() if k not in ("dropped_events", "collector_returncode")})
        trace.sink = cost.SignalSink(output / "signal-trace.jsonl", console=io.StringIO())
        trace.process = subprocess.Popen([sys.executable, "-c",
            'import signal,sys,time; signal.signal(signal.SIGINT,lambda *_: sys.exit(0)); '
            'signal.signal(signal.SIGTERM,lambda *_: sys.exit(7)); print("ready",flush=True); time.sleep(30)'],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, process_group=0)
        self.assertTrue(select.select([trace.process.stdout], [], [], 3)[0])
        self.assertEqual(trace.process.stdout.readline(), b"ready\n")
        self.addCleanup(trace.stop)
        self.addCleanup(trace.process.stdout.close)
        self.addCleanup(trace.process.stderr.close)
        trace.start = lambda: trace
        trace.check()
        self.assertEqual({k: trace.snapshot()[k] for k in HEALTHY}, HEALTHY)
        return trace

    def inject_failure(self, trace, kind):
        if kind == "loss":
            trace._line("Lost 3 events")
        elif kind == "parse":
            trace._line("ERROR unrecognized collector schema")
        elif kind == "reader":
            trace.health["reader_error"] = "OSError"
        elif kind in ("collector-error", "collector-exit"):
            if kind == "collector-error":
                trace.process.terminate()
            else:
                trace.process.send_signal(signal.SIGINT)
            trace.process.wait(timeout=2)
        elif kind == "console":
            trace.sink.console = Mock(write=Mock(side_effect=BrokenPipeError("fixture console failure")))
            trace.sink.emit({"kind": "retention-fixture"})
        elif kind == "file":
            stream = trace.sink.stream
            trace.sink.stream = Mock(write=Mock(side_effect=OSError("fixture file failure")), close=stream.close)
            trace.sink.emit({"kind": "retention-fixture"})
        else:
            self.fail("unknown failure kind")

    def command(self, name, text="", active=False, nested_group=False):
        if not active:
            body = f'import pathlib,sys; pathlib.Path({str(self.root / (name + ".started"))!r}).write_text("started"); sys.stdout.write({text!r})'
        else:
            body = f'''import os,pathlib,signal,subprocess,sys,time
leaf = subprocess.Popen([sys.executable,"-c", "import os,time; print(os.getpid(),flush=True); time.sleep(30)"], stdout=subprocess.PIPE, **({{"process_group": 0}} if {nested_group!r} else {{}}))
pid = int(leaf.stdout.readline())
pathlib.Path({str(self.root / (name + ".leaf"))!r}).write_text(str(pid))
def finish(*_):
    rc = leaf.wait(timeout=1.5)
    pathlib.Path({str(self.root / (name + ".reaped"))!r}).write_text(str(rc))
    sys.exit(0)
signal.signal(signal.SIGTERM, finish)
print("raw active stdout",flush=True)
print("raw active stderr",file=sys.stderr,flush=True)
pathlib.Path({str(self.root / (name + ".started"))!r}).write_text("started")
time.sleep(30)
'''
        return [sys.executable, "-c", body]

    def run_chain(self, kind=None, active=None, between=None, late=False):
        trace = self.trace(self.root / "trace")
        started = []
        original_check = trace.check
        fired = False
        def check():
            nonlocal fired
            if kind and active and not fired and (self.root / (active + ".started")).exists():
                fired = True
                self.inject_failure(trace, kind)
            original_check()
        trace.check = check
        observer = cost.observe_command
        texts = {"compiler-selection": str(self.real) + "\n", "compiler-version": "Lean (version 4.34.1)\n",
                 "compiler-githash": "fixture-githash\n", "judge-lean-producer": "  /fixture path/producer.dll\n"}
        expected = {"judge-build": ["make", "-C", "tools", "dotnet", "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"],
                    "judge-lean-producer": ["bash", "tools/scripts/workflow/judge-lean-producer.sh", str(self.root / "tools/StrataLint.Cli/bin/Release/net10.0")],
                    "compiled-judge-test": ["make", "compiled-judge-test"],
                    "full-lean-report": ["make", "lean-report", "LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build"]}
        def observe(command, cwd, output, name, env, **kwargs):
            nonlocal fired
            if name in expected:
                self.assertEqual(command, expected[name])
            if name == "compiled-judge-test":
                self.assertEqual(env["STRATALINT_LEAN_PRODUCER_DLL"], "/fixture path/producer.dll")
            try:
                rc = observer(self.command(name, texts.get(name, ""), name == active), cwd, output, name, env,
                              interval=.02, signal_trace=kwargs["signal_trace"])
            finally:
                if (self.root / (name + ".started")).exists():
                    started.append(name)
            if kind and not fired and (name == between or (late and name == "full-lean-report")):
                fired = True
                self.inject_failure(trace, kind)
            return rc
        # Sampling is orthogonal to this repair; commands, groups, waits and
        # trace health/sink/collector behavior below are actual local processes.
        with patch.object(cost, "native_binding", return_value={"inputs": {}}), \
                patch.object(cost, "input_binding", return_value={}), \
                patch.object(cost, "SignalTrace", return_value=trace), \
                patch.object(cost, "emit_process_catalog"), \
                patch.object(cost, "capability_preflight", return_value={"status": "passed"}), \
                patch.object(cost, "sample", return_value={"processes": []}), \
                patch.object(cost, "observe_command", side_effect=observe):
            error = None
            rc = None
            begin = time.monotonic()
            try:
                rc = cost.run(self.root, self.output)
            except ValueError as caught:
                error = caught
            elapsed = time.monotonic() - begin
        result = json.loads((self.output / "result.json").read_text())
        inventory = json.loads((self.output / "inventory.json").read_text())
        self.assertIn("result.json", {row["path"] for row in inventory})
        self.assertEqual(result["preflight"]["status"], "passed")
        return rc, error, result, started, elapsed

    def test_healthy_chain_preserves_producer_stdout_and_canonical_invocations(self):
        rc, error, result, started, _ = self.run_chain()
        self.assertEqual(rc, 0)
        self.assertIsNone(error)
        self.assertTrue(result["canonical_chain_complete"])
        self.assertEqual(started[-4:], ["judge-build", "judge-lean-producer", "compiled-judge-test", "full-lean-report"])
        self.assertEqual((self.output / "judge-lean-producer.stdout.log").read_bytes(), b"  /fixture path/producer.dll\n")

    def test_live_failure_stops_reaps_descendants_and_forbids_later_stages(self):
        for active in ("judge-build", "judge-lean-producer", "compiled-judge-test", "full-lean-report"):
            for kind in self.failures:
                with self.subTest(active=active, failure=kind):
                    # Each subcase has an independent bounded command chain.
                    self.fresh_case()
                    unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], process_group=0)
                    try:
                        _, error, result, started, elapsed = self.run_chain(kind, active=active)
                        self.assertIsInstance(error, ValueError)
                        self.assertLess(elapsed, 5)
                        self.assertEqual(started[-1], active)
                        self.assertFalse(result["canonical_chain_complete"])
                        self.assertIsNone(result["canonical_returncode"])
                        self.assertIsNone(result["canonical_failure"])
                        self.assertTrue(result["observer_failure"])
                        self.assertEqual((self.root / (active + ".reaped")).read_text(), str(-signal.SIGTERM))
                        leaf = int((self.root / (active + ".leaf")).read_text())
                        with self.assertRaises(ProcessLookupError):
                            os.kill(leaf, 0)
                        end = json.loads((self.output / "stages.jsonl").read_text().splitlines()[-1])
                        self.assertTrue(end["cleanup"]["root_reaped"])
                        self.assertEqual(end["observer_failure"]["retention"], "censored")
                        self.assertEqual((self.output / (active + ".stdout.log")).read_bytes(), b"raw active stdout\n")
                        self.assertEqual((self.output / (active + ".stderr.log")).read_bytes(), b"raw active stderr\n")
                        self.assertIsNone(unrelated.poll())
                    finally:
                        unrelated.terminate()
                        unrelated.wait(timeout=2)

    def test_between_stage_failure_prevents_producer_and_other_next_operations(self):
        for between in ("compiler-githash", "judge-build", "judge-lean-producer", "compiled-judge-test"):
            for kind in self.failures:
                with self.subTest(between=between, failure=kind):
                    self.fresh_case()
                    _, error, result, started, _ = self.run_chain(kind, between=between)
                    self.assertIsInstance(error, ValueError)
                    self.assertEqual(started[-1], between)
                    self.assertFalse(result["canonical_chain_complete"])
                    self.assertIsNone(result["canonical_returncode"])

    def test_late_full_report_failure_retains_inventory_and_never_claims_complete_chain(self):
        for kind in self.failures:
            with self.subTest(failure=kind):
                self.fresh_case()
                _, error, result, started, _ = self.run_chain(kind, late=True)
                self.assertIsInstance(error, ValueError)
                self.assertFalse(result["canonical_chain_complete"])
                self.assertIsNone(result["canonical_returncode"])
                self.assertEqual(started[-1], "full-lean-report")

    def test_unresponsive_owned_root_is_killed_and_waited(self):
        trace = self.trace(self.output)
        original = trace.check
        marker = self.root / "unresponsive"
        def check():
            if marker.exists():
                trace.health["lost_events"] = 1
            original()
        trace.check = check
        command = [sys.executable, "-c", f'import pathlib,signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); pathlib.Path({str(marker)!r}).touch(); time.sleep(30)']
        with patch.object(cost, "sample", return_value={"processes": []}), self.assertRaises(ValueError):
            cost.observe_command(command, self.root, self.output, "unresponsive", dict(os.environ), signal_trace=trace)
        end = json.loads((self.output / "stages.jsonl").read_text().splitlines()[-1])
        self.assertEqual(end["returncode"], -signal.SIGKILL)
        self.assertTrue(end["cleanup"]["root_reaped"])

    def test_sampled_unrelated_identities_cannot_authorize_signals(self):
        owned = Mock(stop=Mock(return_value={"workload_reaped": True}))
        with patch.object(cost.os, "kill") as kill, patch.object(cost.os, "killpg") as killpg:
            cleanup = cost.stop_owned_command(owned, [{"pid": os.getpid(), "start_ticks": 1}])
        self.assertTrue(cleanup["workload_reaped"])
        owned.stop.assert_called_once_with()
        kill.assert_not_called()
        killpg.assert_not_called()


class ColdCostTests(unittest.TestCase):
    def setUp(self):
        portable_control_flow(self)
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

    def test_fatal_sampling_stops_command_and_keeps_writable_error_log(self):
        command = [sys.executable, "-c", 'import sys,time; print("raw",flush=True); print("err",file=sys.stderr,flush=True); time.sleep(30)']
        def fail_sample(*_args, **_kwargs):
            deadline = time.monotonic() + 3
            while not (self.output / "fixture.stdout.log").read_bytes():
                self.assertLess(time.monotonic(), deadline)
                time.sleep(.01)
            raise OSError("sample unavailable")
        with patch.object(cost, "sample", side_effect=fail_sample), self.assertRaises(OSError):
            cost.observe_command(command, self.root, self.output, "fixture", dict(os.environ), interval=.01)
        self.assertEqual((self.output / "fixture.stdout.log").read_bytes(), b"raw\n")
        self.assertEqual((self.output / "fixture.stderr.log").read_bytes(), b"err\n")
        end = json.loads((self.output / "stages.jsonl").read_text().splitlines()[-1])
        self.assertEqual(end["returncode"], -signal.SIGTERM)
        self.assertTrue(end["cleanup"]["workload_reaped"])
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
                patch.object(cost, "observe_output", side_effect=lambda command, *_args: checked_output(command)), \
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

    def test_recorded_sampler_failure_forbids_next_canonical_operation(self):
        observe_command = cost.observe_command

        def observe(_command, cwd, output, name, _env, **_kwargs):
            # Exercise the existing sampler-error path with a real command;
            # canonical project commands remain private fixtures.
            with patch.object(cost, "sample", side_effect=OSError("private sample failure")):
                return observe_command([sys.executable, "-c", "import time; time.sleep(.05)"],
                                       cwd, output, name, dict(os.environ), interval=.01)

        rc, error, result, observed = self.run_fixture(observe)
        self.assertIsNone(rc)
        self.assertIsInstance(error, ValueError)
        self.assertIsNone(result["canonical_returncode"])
        self.assertFalse(result["canonical_chain_complete"])
        self.assertEqual(len(result["canonical_stages"]), 1)
        self.assertIsNotNone(result["canonical_stages"][0]["returncode"])
        self.assertEqual(observed.call_count, 1)
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


class RequiredLifecycleTests(unittest.TestCase):
    """GoalArtifact report/integration evidence: actual shared lifecycle consumers.

    These bounded private pipes exercise Python observer ownership, not native
    kernel attachment or a complete resource/no-OOM diagnosis.
    """
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="required lifecycle ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def execute(self, body, *args, expected_returncode=0):
        driver = self.root / "driver.py"
        driver.write_text('''import io,json,os,pathlib,runpy,select,signal,subprocess,sys,threading,time
from unittest.mock import Mock,patch
ns=runpy.run_path(sys.argv[1],run_name="fixture_import")
cost=ns["cost"]
if sys.platform != "linux": cost.OwnedCommand=ns["PortableOwnedCommand"]
root=pathlib.Path(sys.argv[2])
''' + body)
        completed = subprocess.run([sys.executable, "-B", str(driver), str(Path(__file__).resolve()),
                                    str(self.root), *args], capture_output=True, timeout=12)
        self.assertEqual(completed.returncode, expected_returncode, completed.stderr.decode(errors="replace"))
        print("LIFECYCLE_FIXTURE " + completed.stdout.decode().strip(), flush=True)
        return json.loads(completed.stdout)

    def test_backpressure_reader_main_and_finish_release_owned_operation(self):
        # The reader and stage-process main consumer contend on an actually full
        # open pipe. A real TERM while contended must still permit owned cleanup.
        body = '''
r,w=os.pipe(); console=os.fdopen(w,"w",buffering=1)
os.set_blocking(w,False); filled=0
try:
    while True: filled+=os.write(w,b"x"*4096)
except BlockingIOError: pass
os.set_blocking(w,True)
assert filled>0 and not select.select([],[w],[],0)[1]
trace=cost.SignalTrace(root); trace.deadline=time.monotonic()+30
trace.sink=cost.SignalSink(root/"trace.jsonl",console=io.StringIO())
trace.process=subprocess.Popen([sys.executable,"-c",'import signal,sys,time; signal.signal(signal.SIGINT,lambda *_: sys.exit(0)); print("D\\tready",flush=True); sys.stdin.readline(); print("D\\tkill\\t100\\t15\\t2\\t0\\t0\\t20\\t20\\t1\\t20\\t20\\t90\\tpython",flush=True); time.sleep(30)'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,process_group=0)
trace.thread=threading.Thread(target=trace._read); trace.thread.start()
assert trace.ready.wait(3)
trace.check()
command=[sys.executable,"-c",'import os,pathlib,time; pathlib.Path('+repr(str(root/"command.pid"))+').write_text(str(os.getpid())); time.sleep(30)']
timer=None
def sample(*_args,**_kwargs):
    global timer
    deadline=time.monotonic()+3
    while not (root/"command.pid").exists():
        assert time.monotonic()<deadline
        time.sleep(.005)
    trace.sink.console=console
    trace.process.stdin.write(b"emit\\n"); trace.process.stdin.flush()
    deadline=time.monotonic()+2
    while not trace.sink.lock.locked():
        assert time.monotonic()<deadline
        time.sleep(.001)
    timer=threading.Timer(.03,lambda: os.kill(os.getpid(),signal.SIGTERM)); timer.start()
    return {"processes":[{"pid":int((root/"command.pid").read_text())}]}
begin=time.monotonic()
try:
    with patch.object(cost,"sample",side_effect=sample):
        cost.observe_command(command,root,root,"backpressure",dict(os.environ),signal_trace=trace)
    raise AssertionError("cancelled observer returned")
except cost.CommandCancelled as error:
    assert error.signum==signal.SIGTERM
finally:
    health=trace.stop()
    if timer: timer.join(timeout=1)
    trace.process.stdin.close(); trace.process.stdout.close(); trace.process.stderr.close()
elapsed=time.monotonic()-begin
assert elapsed<5 and not trace.thread.is_alive() and trace.sink.closed
assert health["dropped_events"]>0 and health["collector_returncode"]==0
assert os.get_blocking(w)
try: os.kill(int((root/"command.pid").read_text()),0)
except ProcessLookupError: pass
else: raise AssertionError("owned command survives")
end=json.loads((root/"stages.jsonl").read_text().splitlines()[-1])
assert end["cleanup"]["workload_reaped"] and end["returncode"] is not None
assert end["observer_failure"]["retention"]=="censored"
terminal=json.loads((root/"trace.jsonl").read_text().splitlines()[-1])
assert terminal["retention"]=="censored" and terminal["dropped_events"]>0
try: cost.require_trace_health(health)
except ValueError: pass
else: raise AssertionError("backpressure accepted")
console.close(); os.close(r)
print(json.dumps({"filled":filled,"elapsed":elapsed,"returncode":end["returncode"]}))
'''
        result = self.execute(body)
        self.assertGreater(result["filled"], 0)
        self.assertLess(result["elapsed"], 5)

    def test_terminal_first_backpressure_censors_local_terminal_without_blocking(self):
        result = self.execute('''
r,w=os.pipe(); console=os.fdopen(w,"w",buffering=1)
os.set_blocking(w,False)
try:
    while True: os.write(w,b"x"*4096)
except BlockingIOError: pass
os.set_blocking(w,True)
trace=cost.SignalTrace(root); trace.health.update(ready=True)
trace.sink=cost.SignalSink(root/"trace.jsonl",console=console)
begin=time.monotonic(); health=trace.stop(); elapsed=time.monotonic()-begin
terminal=json.loads((root/"trace.jsonl").read_text().splitlines()[-1])
assert elapsed<2 and trace.sink.closed and os.get_blocking(w)
assert health["dropped_events"]>0 and terminal["dropped_events"]>0
assert terminal["retention"]=="censored"
console.close(); os.close(r)
print(json.dumps({"elapsed":elapsed}))
''')
        self.assertLess(result["elapsed"], 2)

    def test_healthy_descriptor_console_and_binary_query_keep_exact_bytes_and_status(self):
        result = self.execute('''
r,w=os.pipe(); console=os.fdopen(w,"w",buffering=1); retained=bytearray()
def drain():
    while True:
        block=os.read(r,4096)
        if not block: break
        retained.extend(block)
reader=threading.Thread(target=drain,daemon=True); reader.start()
trace=Mock(sink=cost.SignalSink(root/"trace.jsonl",console=console),snapshot=Mock(return_value=ns["HEALTHY"]))
command=[sys.executable,"-c",'import os; os.write(1,bytes([0,255])+b"binary"+bytes([10]))']
with patch.object(cost,"sample",return_value={"processes":[]}):
    data=cost.observe_output(command,root,root,"query",dict(os.environ),trace)
    status=cost.observe_command([sys.executable,"-c",'import os,sys; os.write(1,bytes([255])+b"raw"); sys.exit(7)'],root,root,"failed",dict(os.environ),signal_sink=trace.sink)
trace.sink.finish({}); console.close(); reader.join(timeout=2); os.close(r)
assert not reader.is_alive() and data==b"\\x00\\xffbinary\\n" and status==7
assert (root/"failed.stdout.log").read_bytes()==b"\\xffraw"
expected=b"".join(b"SIGNAL_DIAGNOSTIC "+line for line in (root/"trace.jsonl").read_bytes().splitlines(keepends=True))
assert retained==expected and trace.sink.dropped_events==0
print(json.dumps({"returncode":status,"bytes":len(retained)}))
''')
        self.assertEqual(result["returncode"], 7)

    def test_actual_late_signals_at_normal_return_shared_handoff(self):
        # One handoff invariant, applied to the existing run/operation/query
        # consumers; actual OS delivery follows the underlying function return.
        body = '''
consumer=sys.argv[3]; signum=int(sys.argv[4]); fired=False
target=(cost.run if consumer=="run" else cost.observe_command).__wrapped__.__code__
def late(frame,event,arg):
    global fired
    if frame.f_code is target and event=="return" and arg is not None and not fired:
        fired=True
        os.kill(os.getpid(),signum)
    return late
sys.settrace(late)
try:
    if consumer=="run":
        fixture=ns["ColdCostTests"](); fixture.setUp()
        try: fixture.run_fixture([0,0,0])
        finally:
            output=fixture.root/"run-observations"
            result=json.loads((output/"result.json").read_text())
            assert not result["canonical_chain_complete"] and result["canonical_returncode"] is None
            assert result["observer_failure"]["signal"]==signum
            assert [s["returncode"] for s in result["canonical_stages"]]==[0,0,0,0]
            inventory=json.loads((output/"inventory.json").read_text())
            row=next(row for row in inventory if row["path"]=="result.json")
            assert row["sha256"]==cost.sha(output/"result.json")
            fixture.doCleanups()
    else:
        command=[sys.executable,"-c",'import os; os.write(1,bytes([0,255])+b"query")']
        with patch.object(cost,"sample",return_value={"processes":[]}):
            if consumer=="query": cost.observe_output(command,root,root,"tail",dict(os.environ),Mock(snapshot=Mock(return_value=ns["HEALTHY"])))
            else: cost.observe_command(command,root,root,"tail",dict(os.environ))
    raise AssertionError("latched cancellation discarded")
except cost.CommandCancelled as error:
    assert fired and error.signum==signum
    assert error.command_returncode==0
    if consumer!="run":
        end=json.loads((root/"stages.jsonl").read_text().splitlines()[-1])
        assert end["returncode"]==0 and end["cleanup"]["workload_reaped"]
        assert (root/"tail.stdout.log").read_bytes()==bytes([0,255])+b"query"
finally: sys.settrace(None)
print(json.dumps({"signal":signum,"consumer":consumer}))
sys.exit(128+signum)
'''
        for consumer, signum in (("run", signal.SIGTERM), ("operation", signal.SIGINT), ("query", signal.SIGHUP)):
            with self.subTest(consumer=consumer):
                self.assertEqual(self.execute(body, consumer, str(int(signum)),
                                              expected_returncode=128+int(signum))["signal"], signum)


class PublicationFailureTests(unittest.TestCase):
    setUp = ColdCostTests.setUp
    run_fixture = ColdCostTests.run_fixture

    def test_final_inventory_failures_censor_result_and_keep_real_stage_codes(self):
        original_sha, original_stat, original_write = cost.sha, Path.stat, cost.write_json
        for kind in ("hash", "stat", "write"):
            with self.subTest(kind=kind):
                self.setUp()
                hashing_result = False
                def hash_file(path):
                    nonlocal hashing_result
                    if path.name == "result.json":
                        hashing_result = True
                        if kind == "hash":
                            raise OSError("inventory hash unavailable")
                    return original_sha(path)
                def stat_file(path, *args, **kwargs):
                    if kind == "stat" and hashing_result and path.name == "result.json":
                        raise OSError("inventory stat unavailable")
                    return original_stat(path, *args, **kwargs)
                def write_file(path, value):
                    if kind == "write" and path.name == "inventory.json":
                        raise OSError("inventory write unavailable")
                    return original_write(path, value)
                with patch.object(cost, "sha", side_effect=hash_file), \
                        patch.object(Path, "stat", stat_file), \
                        patch.object(cost, "write_json", side_effect=write_file):
                    rc, error, result, observe = self.run_fixture([0, 0, 0])
                self.assertIsNone(rc)
                self.assertIsInstance(error, OSError)
                self.assertIsNone(result["canonical_returncode"])
                self.assertFalse(result["canonical_chain_complete"])
                self.assertEqual(result["observer_failure"]["stage"], "artifact-collection")
                self.assertEqual(result["observer_failure"]["retention"], "censored")
                self.assertEqual([s["returncode"] for s in result["canonical_stages"]], [0, 0, 0, 0])
                self.assertEqual(observe.call_count, 3)

    def test_samples_sink_failure_stops_chain_with_error_sink_still_writable(self):
        observe_command, original_append = cost.observe_command, cost.append
        def append_file(path, value):
            if path.name == "samples.jsonl":
                raise OSError("samples sink unavailable")
            return original_append(path, value)
        def observe(_command, cwd, output, name, env, **_kwargs):
            return observe_command([sys.executable, "-c", "import time; time.sleep(30)"],
                                   cwd, output, name, env, interval=.01)
        with patch.object(cost, "append", side_effect=append_file), \
                patch.object(cost, "sample", return_value={"processes": []}):
            _, error, result, observe_mock = self.run_fixture(observe)
        self.assertIsNotNone(error)
        self.assertEqual(observe_mock.call_count, 1)
        self.assertFalse(result["canonical_chain_complete"])
        self.assertIsNone(result["canonical_returncode"])
        self.assertEqual(len(result["canonical_stages"]), 1)
        self.assertEqual(result["canonical_stages"][0]["returncode"], -signal.SIGTERM)
        rows = [json.loads(line) for line in (self.root / "run-observations" / "observer-errors.jsonl").read_text().splitlines()]
        self.assertEqual(rows[0]["error"], "OSError")


class CancellationBehaviorTests(unittest.TestCase):
    """Actual signal delivery; Darwin uses the explicit portable ownership double."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="cancellation ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def cancellation_driver(self, mode):
        # Private fixtures replace canonical queries/commands, never execute them.
        # Trace teardown uses the real SignalTrace.stop and a real private child.
        driver = self.root / "driver.py"
        driver.write_text('''import io,json,os,pathlib,runpy,select,signal,subprocess,sys,time
from unittest.mock import patch
ns=runpy.run_path(sys.argv[1],run_name="fixture_import")
cost=ns["cost"]
if sys.platform != "linux": cost.OwnedCommand=ns["PortableOwnedCommand"]
root=pathlib.Path(sys.argv[2]); mode=sys.argv[3]; output=root/"output"
real=root/"lean"; real.write_bytes(b"private compiler fixture")
trace=cost.SignalTrace(output)
def start():
    trace.health.update(ready=True,lost_events=0,parse_errors=0,reader_error=None)
    trace.sink=cost.SignalSink(output/"signal-trace.jsonl",console=io.StringIO())
    trace.process=subprocess.Popen([sys.executable,"-c",'import signal,sys,time; signal.signal(signal.SIGINT,lambda *_: sys.exit(0)); print("ready",flush=True); time.sleep(30)'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,process_group=0)
    if not select.select([trace.process.stdout],[],[],3)[0]: raise TimeoutError("tracer")
    trace.process.stdout.readline()
    (root/"tracer.pid").write_text(str(trace.process.pid))
    return trace
trace.start=start
cost.SignalTrace=lambda *_args: trace
cost.native_binding=lambda *_args: {"inputs":{}}
cost.input_binding=lambda *_args: {}
cost.emit_process_catalog=lambda *_args: None
cost.capability_preflight=lambda *_args: {"status":"passed"}
cost.sample=lambda *_args,**_kwargs: {"processes":[]}
def query(command,*_args):
    if command[0]=="elan": return str(real).encode()
    if "--version" in command: return b"Lean (version 4.34.1)"
    if "--githash" in command: return b"fixture"
    raise AssertionError("next producer must never launch")
cost.observe_output=query
observe=cost.observe_command
original_popen=cost.subprocess.Popen
def post_spawn(*args,**kwargs):
    child=original_popen(*args,**kwargs)
    (root/"spawn.pid").write_text(str(child.pid))
    os.kill(os.getpid(),signal.SIGINT)
    return child
def command(_command,cwd,output,name,env,**kwargs):
    body='import os,pathlib,time; pathlib.Path('+repr(str(root/"command.pid"))+').write_text(str(os.getpid())); pathlib.Path('+repr(str(root/"ready"))+').touch(); time.sleep(30)'
    if mode=="post-spawn":
        with patch.object(cost.subprocess,"Popen",side_effect=post_spawn):
            return observe([sys.executable,"-c",body],cwd,output,name,env,signal_trace=kwargs["signal_trace"])
    return observe([sys.executable,"-c",body],cwd,output,name,env,signal_trace=kwargs["signal_trace"])
cost.observe_command=command
try:
    cost.run(root,output)
except cost.CommandCancelled as error:
    sys.exit(128+error.signum)
finally:
    if trace.process:
        trace.process.stdout.close(); trace.process.stderr.close()
''')
        return subprocess.Popen([sys.executable, str(driver), str(Path(__file__).resolve()), str(self.root), mode],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, process_group=0)

    def check_signal(self, signum, mode="external"):
        witness = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], process_group=0)
        driver = self.cancellation_driver(mode)
        try:
            if mode == "external":
                deadline = time.monotonic() + 5
                while not (self.root / "ready").exists():
                    self.assertIsNone(driver.poll())
                    self.assertLess(time.monotonic(), deadline)
                    time.sleep(.01)
                os.kill(driver.pid, signum)
            stdout, stderr = driver.communicate(timeout=8)
            self.assertEqual(driver.returncode, 128 + signum, stderr.decode())
            result = json.loads((self.root / "output/result.json").read_text())
            self.assertIsNone(result["canonical_returncode"])
            self.assertFalse(result["canonical_chain_complete"])
            self.assertEqual(result["observer_failure"]["signal"], signum)
            self.assertEqual(result["trace_health"]["collector_returncode"], 0)
            self.assertEqual(len(result["canonical_stages"]), 1)
            self.assertIsNotNone(result["canonical_stages"][0]["returncode"])
            ends = [json.loads(line) for line in (self.root / "output/stages.jsonl").read_text().splitlines()
                    if json.loads(line)["kind"] == "stage-end"]
            self.assertEqual(len(ends), 1)
            self.assertTrue(ends[0]["cleanup"]["workload_reaped"])
            for name in ("command.pid", "spawn.pid", "tracer.pid"):
                path = self.root / name
                if path.exists():
                    with self.assertRaises(ProcessLookupError):
                        os.kill(int(path.read_text()), 0)
            self.assertIsNone(witness.poll())
        finally:
            if driver.poll() is None:
                driver.terminate()
                try:
                    driver.wait(timeout=6)
                except subprocess.TimeoutExpired:
                    driver.kill()
            driver.communicate(timeout=2)
            witness.terminate()
            witness.wait(timeout=2)

    def test_actual_term(self):
        self.check_signal(signal.SIGTERM)

    def test_actual_hup(self):
        self.check_signal(signal.SIGHUP)

    def test_post_popen_sigint(self):
        self.check_signal(signal.SIGINT, "post-spawn")


@unittest.skipUnless(sys.platform == "linux", "genuine Linux subreaper ownership pending; portable fixtures are not Linux proof")
class LinuxOwnershipTests(CancellationBehaviorTests):
    """Native capability fixtures: no sampler, compiler or report execution."""
    def orphan_case(self, nested, root_waits):
        pidfile = self.root / "leaf.pid"
        ready = self.root / "root.ready"
        leaf_body = 'import os,signal,sys,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); print(os.getpid(),flush=True); time.sleep(30)'
        body = f'''import os,pathlib,subprocess,sys,time
assert sys.argv[1] == "literal $argument"
assert os.environ["OWNERSHIP_TEST_ARGUMENT"] == "literal environment"
os.write(1,b"owned\\x00stdout\\n")
os.write(2,b"owned stderr\\n")
leaf=subprocess.Popen([sys.executable,"-c",{leaf_body!r}],stdout=subprocess.PIPE,process_group={0 if nested else 'None'})
pathlib.Path({str(pidfile)!r}).write_text(leaf.stdout.readline().decode().strip())
pathlib.Path({str(ready)!r}).touch()
{'time.sleep(30)' if root_waits else 'sys.exit(0)'}
'''
        witness = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], process_group=0)
        with (self.root / "stdout").open("wb") as stdout, (self.root / "stderr").open("wb") as stderr:
            child = cost.OwnedCommand([sys.executable, "-c", body, "literal $argument"], cwd=self.root,
                                      env=dict(os.environ, OWNERSHIP_TEST_ARGUMENT="literal environment"),
                                      stdout=stdout, stderr=stderr)
            try:
                deadline = time.monotonic() + 5
                while not ready.exists():
                    child.poll()
                    self.assertLess(time.monotonic(), deadline)
                    time.sleep(.01)
                leaf = int(pidfile.read_text())
                child.poll()
                self.assertEqual(os.getpgid(leaf), leaf if nested else child.pid)
                # No observer ancestry snapshot has ever occurred. Kernel
                # adoption, not remembered PPID/group, must retain ownership.
                if root_waits:
                    cleanup = cost.stop_owned_command(child)
                else:
                    while child.returncode is None:
                        child.poll()
                        self.assertLess(time.monotonic(), deadline)
                        time.sleep(.01)
                    self.assertEqual(cost.proc_row(Path("/proc") / str(leaf))["ppid"], child.process.pid)
                    deadline = time.monotonic() + 6
                    while child.poll() is None:
                        self.assertLess(time.monotonic(), deadline)
                        time.sleep(.01)
                    cleanup = child.cleanup
                self.assertTrue(cleanup["root_reaped"])
                self.assertTrue(cleanup["workload_reaped"])
                self.assertIn(leaf, cleanup["identity_checked_descendants"])
                self.assertEqual(child.returncode, -signal.SIGTERM if root_waits else 0)
                for pid in (leaf, child.pid, child.process.pid):
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
                self.assertIsNone(witness.poll())
                self.assertEqual((self.root / "stdout").read_bytes(), b"owned\x00stdout\n")
                self.assertEqual((self.root / "stderr").read_bytes(), b"owned stderr\n")
            finally:
                if child.process.poll() is None:
                    child.stop()
                child.close()
                witness.terminate()
                witness.wait(timeout=2)

    def test_early_leader_exit_before_first_snapshot(self):
        self.orphan_case(nested=False, root_waits=False)

    def test_term_ignoring_original_group_after_root_term(self):
        self.orphan_case(nested=False, root_waits=True)

    def test_nested_group_reparent_before_first_snapshot(self):
        self.orphan_case(nested=True, root_waits=False)


class OwnershipUnavailableTests(unittest.TestCase):
    def test_non_linux_fails_closed_before_command_spawn(self):
        with patch.object(cost.sys, "platform", "darwin"), patch.object(cost.subprocess, "Popen") as spawn:
            with self.assertRaisesRegex(ValueError, "subreaper unavailable"):
                cost.enable_subreaper()
        spawn.assert_not_called()

    @unittest.skipIf(sys.platform == "linux", "uses the actual non-Linux host rejection")
    def test_actual_non_linux_supervisor_never_launches_workload(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            marker = output / "must-not-launch"
            with self.assertRaisesRegex(ValueError, "owned workload cleanup unavailable"):
                cost.observe_command([sys.executable, "-c", f'from pathlib import Path; Path({str(marker)!r}).touch()'],
                                     output, output, "unsupported", dict(os.environ))
            self.assertFalse(marker.exists())
            end = json.loads((output / "stages.jsonl").read_text().splitlines()[-1])
            self.assertEqual(end["observer_failure"]["retention"], "censored")


if __name__ == "__main__":
    unittest.main()
