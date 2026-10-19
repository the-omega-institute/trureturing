"""Real process behavior for the opt-in observer; no workflow-text assertions."""
import ctypes
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

REPO = Path(__file__).resolve().parents[4]
WRAPPER = REPO / "tools/scripts/report/runner-diagnostics.py"
PREFIX = "RUNNER_DIAGNOSTICS "


def load():
    spec = importlib.util.spec_from_file_location("runner_diagnostics", WRAPPER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def records(text):
    return [json.loads(line[len(PREFIX):]) for line in text.splitlines() if line.startswith(PREFIX)]


def until(predicate):
    deadline = time.monotonic() + 15
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.02)
    raise AssertionError("process handshake deadline expired")


def worker(directory, allow_ptrace):
    directory = Path(directory)
    libc = ctypes.CDLL(None, use_errno=True)
    assert libc.prctl(15, b"Runner.Worker", 0, 0, 0) == 0
    if allow_ptrace:
        assert libc.prctl(0x59616d61, ctypes.c_ulong(-1), 0, 0, 0) == 0
    else:
        assert libc.prctl(4, 0, 0, 0, 0) == 0  # Require privileged attach, even with Yama disabled.
    def received(number, _frame):
        with (directory / "worker-signals").open("a") as stream:
            stream.write(str(number) + "\n")
    signal.signal(signal.SIGUSR1, received)
    signal.signal(signal.SIGTERM, received)
    child = subprocess.Popen([sys.executable, "-B", str(WRAPPER), "--", sys.executable,
                              "-B", __file__, "--business", str(directory)],
                             env=dict(os.environ, STRATALINT_RUNNER_DIAGNOSTICS="true"))
    (directory / "wrapper-pid").write_text(str(child.pid))
    code = child.wait()
    (directory / "business-exit").write_text(str(code))
    return code


def business(directory):
    directory = Path(directory)
    child = subprocess.Popen([sys.executable, "-c",
        "import signal,sys,time; from pathlib import Path; "
        "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0)); "
        "Path(sys.argv[1]).touch(); time.sleep(60)", str(directory / "grandchild-ready")])
    (directory / "grandchild-pid").write_text(str(child.pid))
    cancelled = []
    signal.signal(signal.SIGTERM, lambda *_: cancelled.append(True))
    until(lambda: (directory / "grandchild-ready").exists())
    (directory / "business-ready").touch()
    try:
        until(lambda: bool(cancelled) or (directory / "release").exists())
    finally:
        if child.poll() is None:
            child.terminate()
        child.wait(timeout=3)
        (directory / "grandchild-joined").touch()
    return 19 if cancelled else 7


class RunnerDiagnosticsTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="runner-diagnostics-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)

    def run_wrapper(self, setting, code=7):
        env = dict(os.environ)
        if setting is None:
            env.pop("STRATALINT_RUNNER_DIAGNOSTICS", None)
        else:
            env["STRATALINT_RUNNER_DIAGNOSTICS"] = setting
        command = [sys.executable, "-B", str(WRAPPER), "--", sys.executable, "-c",
                   "import json,os,sys; print(json.dumps([os.getpid(),sys.argv[1:]])); "
                   "sys.exit(" + str(code) + ")", "literal space", "$(literal)"]
        process = subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True)
        out, err = process.communicate(timeout=10)
        return process, out, err

    def test_disabled_exec_preserves_pid_argv_and_exit(self):
        for setting in (None, "false", "1", "True"):
            for code in (0, 7):
                process, out, err = self.run_wrapper(setting, code)
                self.assertEqual(code, process.returncode)
                self.assertEqual([process.pid, ["literal space", "$(literal)"]], json.loads(out))
                self.assertEqual("", err)

    def test_true_enables_observation_and_preserves_business_exit(self):
        for code in (0, 7):
            process, out, err = self.run_wrapper("true", code)
            self.assertEqual(code, process.returncode, out + err)
            self.assertTrue(records(out))
            self.assertNotIn("Traceback", err)

    def test_nonlinux_is_explicit_and_transparent(self):
        harness = ("import importlib.util,sys; "
                   "s=importlib.util.spec_from_file_location('d',sys.argv[1]); "
                   "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
                   "sys.platform='darwin'; sys.argv=sys.argv[1:]; m.main()")
        result = subprocess.run([sys.executable, "-B", "-c", harness, str(WRAPPER), "--",
                                 sys.executable, "-c", "raise SystemExit(7)"],
                                env=dict(os.environ, STRATALINT_RUNNER_DIAGNOSTICS="true"),
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(7, result.returncode)
        self.assertEqual("linux-only", records(result.stdout)[0]["reason"])

    def test_observer_failure_preserves_exit_and_redacts_error(self):
        module = load()
        with mock.patch.object(module.Observer, "start", side_effect=RuntimeError("PRIVATE_ENV")), \
                mock.patch.object(module.os, "write", side_effect=lambda fd, data: len(data)) as output:
            self.assertEqual(7, module.observed([sys.executable, "-c", "raise SystemExit(7)"]))
        lines = "\n".join(call.args[1].decode() for call in output.call_args_list)
        self.assertNotIn("PRIVATE_ENV", lines)
        self.assertIn('"reason": "observer-start"', lines)
        self.assertIn('"sampler_alive": false', lines)

    def test_missing_tool_permissions_and_early_observer_exit_fail_open(self):
        module = load()
        fake = self.directory / "strace"
        fake.write_text("#!" + sys.executable + "\nimport sys\n"
                        "print('ptrace denied PRIVATE_ENV', flush=True)\nsys.exit(23)\n")
        fake.chmod(0o755)
        worker = dict(pid=os.getpid(), name="Runner.Worker", ppid=os.getppid(),
                      pgid=0, sid=0, starttime=0)
        for installed in (False, True):
            with mock.patch.object(module, "worker_ancestor", return_value=worker), \
                    mock.patch.object(module.shutil, "which", side_effect=lambda name:
                                      str(fake) if installed and name == "strace" else None), \
                    mock.patch.dict(os.environ, PATH=str(self.directory)), \
                    mock.patch.object(module.os, "write", side_effect=lambda fd, data: len(data)) as output:
                self.assertEqual(7, module.observed([sys.executable, "-c", "raise SystemExit(7)"]))
            lines = "\n".join(call.args[1].decode() for call in output.call_args_list)
            self.assertNotIn("PRIVATE_ENV", lines)
            self.assertIn('"sampler_alive": false', lines)
            if installed:
                self.assertIn('"exit_code": 23', lines)
                self.assertIn('"reader_alive": false', lines)
                self.assertIn('"reason": "ptrace-or-strace-capability"', lines)
            else:
                self.assertIn('"reason": "strace-not-installed"', lines)

    def test_memory_uses_cgroup_current_limit_and_oom_events(self):
        module = load()
        for name, value in {"memory.current": "1234", "memory.max": "max",
                            "memory.swap.current": "12", "memory.swap.max": "100",
                            "memory.events": "low 0\noom 2\noom_kill 1\n",
                            "memory.pressure": "some avg10=1.25 avg60=2.50 avg300=3.75 total=10\n"
                                               "full avg10=0.25 avg60=0.50 avg300=0.75 total=5\n"}.items():
            (self.directory / name).write_text(value)
        sample = module.memory_sample(self.directory)
        self.assertEqual(1234, sample["memory.current"])
        self.assertEqual("max", sample["memory.max"])
        self.assertEqual(12, sample["memory.swap.current"])
        self.assertEqual(2, sample["memory.events"]["oom"])
        self.assertEqual(1, sample["memory.events"]["oom_kill"])
        self.assertEqual(1.25, sample["memory.pressure"]["some"]["avg10"])
        self.assertEqual(3.75, sample["memory.pressure"]["some"]["avg300"])
        self.assertEqual(5, sample["memory.pressure"]["full"]["total"])

    def test_dispatch_adds_diagnostics_only_for_literal_true(self):
        sys.path.insert(0, str(REPO / "tools/scripts/worktree"))
        self.addCleanup(lambda: sys.path.remove(str(REPO / "tools/scripts/worktree")))
        import lean_pr_cache as cache
        identity = dict(repository="owner/repo", target_ref="refs/heads/dev", merge="a" * 40)
        for setting in ("false", "true", "1", "True"):
            with mock.patch.object(cache, "source_identity", return_value=identity), \
                    mock.patch.object(cache, "validate_remote"), \
                    mock.patch.object(cache.actions, "output"), \
                    mock.patch.object(cache, "receipt"), \
                    mock.patch.object(cache, "api", return_value={"workflow_run_id": 123}) as api, \
                    mock.patch.dict(os.environ, STRATALINT_RUNNER_DIAGNOSTICS=setting):
                cache.dispatch(REPO)
            inputs = api.call_args.args[2]["inputs"]
            expected = dict(operation="pr", source_ref="refs/heads/dev", source_sha="a" * 40,
                            pr_source=json.dumps(identity, separators=(",", ":")))
            if setting == "true":
                expected["runner_diagnostics"] = "true"
            self.assertEqual(expected, inputs)

    def test_console_failure_and_partial_writes_preserve_exit(self):
        program = ("import importlib.util,sys; "
                   "s=importlib.util.spec_from_file_location('d',sys.argv[1]); "
                   "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
                   "m.Observer.start=lambda self: None; "
                   "raise SystemExit(m.observed([sys.executable,'-c','raise SystemExit(7)']))")
        child = subprocess.Popen([sys.executable, "-B", "-c", program, str(WRAPPER)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        child.stdout.close()
        error = child.stderr.read()
        self.assertEqual(7, child.wait(timeout=5), error)
        self.assertEqual("", error)
        child.stderr.close()
        module, writes, calls = load(), [], []
        def partial(_fd, data):
            calls.append(True)
            if len(calls) == 1:
                raise InterruptedError()
            count = min(3, len(data))
            writes.append(data[:count])
            return count
        with mock.patch.object(module.os, "write", side_effect=partial):
            module.emit("signal", si_pid=123)
        text = b"".join(writes).decode()
        self.assertEqual(123, records(text)[0]["si_pid"])
        self.assertTrue(text.endswith("\n"))

    def test_partial_tracer_start_failure_still_reaps_real_process(self):
        module = load()
        fake = self.directory / "strace"
        fake.write_text("#!" + sys.executable + "\nimport time\ntime.sleep(60)\n")
        fake.chmod(0o755)
        observer = module.Observer()
        def own_identity(pid):
            return dict(pid=pid, name="strace", ppid=os.getpid(), pgid=pid, sid=pid, starttime=1)
        with mock.patch.dict(os.environ, PATH=str(self.directory)), \
                mock.patch.object(module, "identity", side_effect=own_identity), \
                mock.patch.object(module.threading.Thread, "start", side_effect=RuntimeError("thread-start")):
            with self.assertRaises(RuntimeError):
                observer.start_trace(dict(pid=os.getpid()), [])
            child = observer.tracer
            observer.close()
        self.assertIsNotNone(child.returncode)
        with self.assertRaises(ProcessLookupError):
            os.kill(child.pid, 0)

    def test_stale_process_or_group_identity_cannot_receive_cleanup(self):
        module = load()
        record = dict(pid=123, name="strace", ppid=12, pgid=123, sid=123, starttime=5)
        for changed in (dict(record, starttime=6), dict(record, pgid=456), dict(record, sid=456)):
            with mock.patch.object(module, "identity", return_value=changed), \
                    mock.patch.object(module.os, "killpg") as kill:
                process = mock.Mock(pid=123)
                process.poll.return_value = None
                module.own_group(process, record, signal.SIGTERM)
                kill.assert_not_called()
        with mock.patch.object(module, "identity", return_value=dict(record, starttime=6)), \
                mock.patch.object(module.os, "kill") as kill:
            self.assertEqual([], module.stop_privileged_tracer(123, 5, signal.SIGTERM))
            kill.assert_not_called()

    def test_cleanup_failure_is_redacted_and_keeps_business_exit(self):
        module = load()
        with mock.patch.object(module.Observer, "start"), \
                mock.patch.object(module.Observer, "close", side_effect=PermissionError("PRIVATE_ENV")), \
                mock.patch.object(module.os, "write", side_effect=lambda fd, data: len(data)) as output:
            self.assertEqual(7, module.observed([sys.executable, "-c", "raise SystemExit(7)"]))
        lines = "\n".join(call.args[1].decode() for call in output.call_args_list)
        self.assertNotIn("PRIVATE_ENV", lines)
        self.assertIn('"reason": "observer-close"', lines)


    @unittest.skipUnless(sys.platform == "linux", "Linux ptrace behavior")
    def test_linux_signal_sender_and_term_join_entire_business_tree(self):
        self.linux_worker(True, True)

    @unittest.skipUnless(sys.platform == "linux", "Linux sudo ptrace behavior")
    def test_linux_sudo_observer_detaches_without_signalling_worker(self):
        if os.geteuid() == 0:
            self.skipTest("root attaches directly; sudo path needs a non-root runner")
        self.assertIsNotNone(shutil.which("sudo"), "Linux CI must exercise sudo fallback")
        self.linux_worker(False, False)

    def linux_worker(self, allow_ptrace, cancel):
        self.assertIsNotNone(shutil.which("strace"), "Linux CI must exercise real strace")
        log = self.directory / "console"
        stream = log.open("w")
        self.addCleanup(stream.close)
        process = subprocess.Popen([sys.executable, "-B", __file__, "--worker",
                                    str(self.directory), "1" if allow_ptrace else "0"],
                                   stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        def cleanup():
            if process.poll() is None:
                (self.directory / "release").touch()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait(timeout=3)
        self.addCleanup(cleanup)
        until(lambda: (self.directory / "business-ready").exists())
        until(lambda: any(item["kind"] == "attached" for item in records(log.read_text())))
        sender = subprocess.run([sys.executable, "-c",
            "import os,signal,sys; print(os.getpid(),flush=True); os.kill(int(sys.argv[1]),signal.SIGUSR1)",
            str(process.pid)], capture_output=True, text=True, check=True, timeout=3)
        sender_pid = sender.stdout.strip()
        until(lambda: any(item["kind"] == "signal" and item.get("si_pid") == sender_pid
                          for item in records(log.read_text())))
        grandchild = int((self.directory / "grandchild-pid").read_text())
        if cancel:
            os.kill(int((self.directory / "wrapper-pid").read_text()), signal.SIGTERM)
        else:
            (self.directory / "release").touch()
        self.assertEqual(19 if cancel else 7, process.wait(timeout=10), log.read_text())
        output = log.read_text()
        observations = records(output)
        self.assertIn('"sampler_alive": false', output)
        self.assertIn('"reader_alive": false', output)
        self.assertTrue((self.directory / "grandchild-joined").exists())
        with self.assertRaises(ProcessLookupError):
            os.kill(grandchild, 0)
        self.assertEqual([str(signal.SIGUSR1)],
                         (self.directory / "worker-signals").read_text().splitlines())
        joins = [item for item in observations if item["kind"] == "tracer_joined"]
        self.assertTrue(joins)
        if not allow_ptrace:
            self.assertTrue(any(item["stopped_tracer_pids"] for item in joins), output)
        for item in observations:
            if item["kind"] == "tracer_joined":
                for pid in [item["pid"], *item["stopped_tracer_pids"]]:
                    self.assertNotEqual(process.pid, pid)
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
        self.assertTrue(any(item["kind"] == "memory" and "MemAvailable_kb" in item
                            for item in observations))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--worker":
        raise SystemExit(worker(sys.argv[2], sys.argv[3] == "1"))
    if len(sys.argv) > 1 and sys.argv[1] == "--business":
        raise SystemExit(business(sys.argv[2]))
    unittest.main()
