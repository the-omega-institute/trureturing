import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
# A timeout is only an infrastructure hang guard; sequencing uses pipe messages.
HANG_GUARD = 30
CONFIG = {
    "dimensions": [24, 32, 40, 48, 55], "seed_steps": 5000, "base_seed": 1005040,
    "learning_rate": 0.01, "minimum_learning_rate": 0.001, "batch_steps": 25,
    "log_max_bytes": 1048576, "log_backups": 3, "verification_gap": 1e-6,
    "verification_interval_steps": 1000, "verification_chunk_size": 256,
    "mps_memory_fraction": 0.25,
}


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + "\n").encode()


class LifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="gpu5040-launcher-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.state = self.root / "state"
        self.state.mkdir()
        self.program = self.root / "program"
        self.program.mkdir()
        self.launcher = self.program / "gpu_bounded_launcher.py"
        shutil.copyfile(HERE / "gpu_bounded_launcher.py", self.launcher)
        shutil.copyfile(HERE / "fixture_worker.py", self.program / "gpu_worker.py")
        shutil.copyfile(HERE / "state_store.py", self.program / "state_store.py")
        shutil.copyfile(HERE / "search_config.py", self.program / "search_config.py")
        (self.state / "latest.pt").write_bytes(b"fixture checkpoint 123")
        self.before = {
            "schema": 2, "pid": 1, "phase": "stopped", "stop_reason": "STOP", "error": None,
            "checkpoint_saved": True, "state_directory": str(self.state),
            "latest_checkpoint": str(self.state / "latest.pt"), "config": copy.deepcopy(CONFIG),
            "config_sha256": hashlib.sha256(encode(CONFIG)).hexdigest(),
            "source_sha256": "a" * 64,
            "history_db": str(self.root / "history.sqlite3"),
            "progress": {"total_steps": 123, "run_index": 0, "iteration": 123},
        }
        self.save_before()
        self.options = {"scenario": "success"}
        self.events = []

    def save_before(self):
        self.before["progress"].setdefault("skipped_trials", 0)
        self.before["progress"].setdefault("traversal_start_steps", 0)
        self.before["session"] = {"id": "baseline"}
        self.before["checkpoint_receipt"] = {
            "sha256": hashlib.sha256((self.state / "latest.pt").read_bytes()).hexdigest(),
            "session_id": "baseline", "pid": self.before["pid"],
            "progress": copy.deepcopy(self.before["progress"])}
        (self.state / "status.json").write_bytes(encode(self.before))

    def spawn(self, scenario="success", command=None, **options):
        self.events = []
        self.options = {"scenario": scenario, **options}
        (self.state / "fixture-options.json").write_bytes(encode(self.options))
        process = subprocess.Popen(command or [sys.executable, str(self.launcher),
                                               "--state-dir", str(self.state)],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, cwd=self.program, start_new_session=True, bufsize=0,
                                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        self.addCleanup(self.reap, process)
        return process

    def reap(self, process):
        if process.poll() is None:
            process.kill()
        process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def event(self, process, expected):
        ready, _, _ = select.select([process.stdout], [], [], HANG_GUARD)
        if not ready:
            raise RuntimeError("INFRASTRUCTURE_UNRESOLVED: pipe hang guard")
        line = process.stdout.readline().decode().strip()
        self.events.append(line)
        self.assertEqual(expected, line)

    def finish(self, process, release=False):
        try:
            stdout, stderr = process.communicate(b"release\n" if release else None,
                                                 timeout=HANG_GUARD)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("INFRASTRUCTURE_UNRESOLVED: subprocess hang guard") from error
        record = {"test": self.id(), "scenario": self.options["scenario"],
                  "launcher_exit": process.returncode, "events": self.events,
                  "stdout": stdout.decode(), "stderr": stderr.decode()}
        self.last_result = record
        marker = self.state / "child-started.json"
        self.child_started = marker.exists()
        if marker.exists():
            pid = json.loads(marker.read_text())["pid"]
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)
            marker.unlink()
        return process.returncode

    def test_expected_completion_and_next_resume(self):
        for start in (123, 25123):
            self.assertEqual(0, self.finish(self.spawn()), self.last_result)
            status = json.loads((self.state / "status.json").read_text())
            self.assertEqual(start + 25000, status["progress"]["total_steps"])
            self.assertEqual(start, status["session"]["resumed_from"]["total_steps"])
            self.assertEqual(CONFIG, status["config"])

    def test_round_is_derived_for_a_different_config(self):
        self.before["config"].update(dimensions=[24, 55], seed_steps=100)
        self.before["config_sha256"] = hashlib.sha256(encode(self.before["config"])).hexdigest()
        self.before["progress"] = {"total_steps": 123, "run_index": 1, "iteration": 23}
        self.save_before()
        self.assertEqual(0, self.finish(self.spawn()))
        self.assertEqual(323, json.loads((self.state / "status.json").read_text())["progress"]["total_steps"])

    def test_stop_before_start_does_not_create_child(self):
        (self.state / "STOP").touch()
        self.assertNotEqual(0, self.finish(self.spawn()))
        self.assertFalse(self.child_started)
        self.assertEqual(b"fixture checkpoint 123", (self.state / "latest.pt").read_bytes())

    def test_stop_during_child_retains_graceful_checkpoint(self):
        process = self.spawn("stop", barrier=True)
        self.event(process, "READY")
        (self.state / "STOP").touch()
        self.assertNotEqual(0, self.finish(process, release=True))
        self.assertEqual(b"fixture checkpoint 124", (self.state / "latest.pt").read_bytes())

    def test_stop_after_max_steps_status_suppresses_restart(self):
        process = self.spawn(terminal_barrier=True)
        self.event(process, "TERMINAL")
        (self.state / "STOP").touch()
        self.assertNotEqual(0, self.finish(process, release=True))

    def test_stop_reason_remains_a_stop_after_file_removed(self):
        self.assertNotEqual(0, self.finish(self.spawn("stop")))

    def test_child_failure_and_invalid_terminal_evidence(self):
        for scenario in ("failure", "failure_after_status", "stale", "malformed", "missing_status",
                         "changed_config", "no_checkpoint", "missing_checkpoint", "empty_checkpoint"):
            with self.subTest(scenario=scenario):
                (self.state / "latest.pt").write_bytes(b"fixture checkpoint 123")
                self.save_before()
                self.assertNotEqual(0, self.finish(self.spawn(scenario)))
                self.assertTrue(self.child_started, self.last_result)

    def test_terminal_fields_are_all_required(self):
        patches = [
            {"phase": "running"}, {"stop_reason": "max_seconds"}, {"stop_reason": "SIGTERM"},
            {"checkpoint_saved": False}, {"checkpoint_saved": 1}, {"error": "failed"},
            {"pid": 1}, {"source_sha256": "b" * 64}, {"config_sha256": "b" * 64},
            {"schema": 3}, {"state_directory": "/wrong"}, {"latest_checkpoint": "/wrong"},
            {"progress": {"total_steps": 25122, "run_index": 5, "iteration": 122}},
            {"progress": {"total_steps": 25123, "run_index": 5, "iteration": 122}},
            {"session": {"start_total_steps": 123, "completed_steps": 24999,
                         "resumed_from": self.before["progress"]}},
            {"session": {"start_total_steps": 124, "completed_steps": 25000,
                         "resumed_from": self.before["progress"]}},
            {"session": {"start_total_steps": 123, "completed_steps": 25000,
                         "resumed_from": {"total_steps": 123, "run_index": 0, "iteration": 122}}},
        ]
        for patch in patches:
            with self.subTest(patch=patch):
                self.save_before()
                self.assertNotEqual(0, self.finish(self.spawn(terminal_patch=patch)))

    def test_malformed_or_missing_baseline_does_not_create_child(self):
        valid = copy.deepcopy(self.before)
        for patch in ({"config": []}, {"config_sha256": "b" * 64}, {"checkpoint_saved": False},
                      {"phase": "error"}, {"progress": {"total_steps": True}},
                      {"progress": {"total_steps": 123, "run_index": 0, "iteration": 124}}):
            with self.subTest(patch=patch):
                self.before = {**valid, **patch}
                self.save_before()
                self.assertNotEqual(0, self.finish(self.spawn()))
                self.assertFalse(self.child_started)
        for value in (b"{broken", b"[]", b"null", None):
            with self.subTest(value=value):
                path = self.state / "status.json"
                if value is None:
                    path.unlink()
                else:
                    path.write_bytes(value)
                self.assertNotEqual(0, self.finish(self.spawn()))
                self.assertFalse(self.child_started)

    def test_missing_checkpoint_does_not_create_child(self):
        (self.state / "latest.pt").unlink()
        self.assertNotEqual(0, self.finish(self.spawn()))
        self.assertFalse(self.child_started)

    def test_invalid_round_inputs_do_not_create_child(self):
        for changes in ({"seed_steps": 0}, {"seed_steps": True}, {"seed_steps": 1.5},
                        {"dimensions": []}, {"dimensions": [24, 24]}, {"dimensions": [True]}):
            with self.subTest(changes=changes):
                self.before["config"] = {**CONFIG, **changes}
                self.before["config_sha256"] = hashlib.sha256(encode(self.before["config"])).hexdigest()
                self.save_before()
                self.assertNotEqual(0, self.finish(self.spawn()))
                self.assertFalse(self.child_started)

    def test_existing_worker_lock_refusal_is_not_retried(self):
        with open(self.root / ".gpu-worker.lock", "a+b") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertNotEqual(0, self.finish(self.spawn()))
        self.assertFalse(self.child_started)

    def test_skipped_trials_are_not_charged_as_optimizer_updates(self):
        self.assertEqual(0, self.finish(self.spawn(skipped_work=7)))
        after = json.loads((self.state / "status.json").read_text())
        self.assertEqual(25123, after["progress"]["total_steps"])
        self.assertEqual(12, after["progress"]["run_index"])
        self.assertEqual(7, after["progress"]["skipped_trials"])

    def test_checkpoint_digest_and_invocation_are_checked(self):
        for patch in ({"sha256": "b" * 64}, {"session_id": "stale"}, {"pid": 1},
                      {"progress": self.before["progress"]}):
            with self.subTest(patch=patch):
                self.save_before()
                self.assertEqual(1, self.finish(self.spawn(receipt_patch=patch)))

    def analytic_before(self, exhausted=False, no_checkpoint=False):
        from search_config import ANALYTIC_ALGORITHM, Config, descriptor, identity, load_initializer
        from test_trial_history import RUNTIME
        config = Config(dimensions=(55,), seed_steps=6, base_seed=0)
        self.before["config"].update(dimensions=[55], seed_steps=6, base_seed=0)
        spec = load_initializer(HERE.parents[3] /
            "Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json")[0]
        desc = descriptor(config, 55, 0, RUNTIME, spec, "a" * 64)
        self.before.update(algorithm=ANALYTIC_ALGORITHM, runtime=RUNTIME,
                           trial={"identity": identity(desc), "descriptor": desc, "terminal": exhausted})
        self.before["config_sha256"] = hashlib.sha256(encode(self.before["config"])).hexdigest()
        self.before["progress"] = {"total_steps": 6 if exhausted else 3,
            "run_index": 0, "iteration": 6 if exhausted else 3,
            "skipped_trials": 0, "traversal_start_steps": 0}
        if exhausted:
            self.before.update(stop_reason="exhausted", exhaustion={"identity": identity(desc), "descriptor": desc})
        self.save_before()
        if no_checkpoint:
            (self.state / "latest.pt").unlink()
            self.before.update(checkpoint_saved=False, checkpoint_receipt=None, trial=None)
            self.before["progress"].update(total_steps=0, run_index=1, iteration=0, skipped_trials=1)
            (self.state / "status.json").write_bytes(encode(self.before))

    def test_analytic_terminal_receipt_is_nonrepeating(self):
        self.analytic_before()
        exhausted = {"identity": self.before["trial"]["identity"],
                     "descriptor": self.before["trial"]["descriptor"]}
        self.assertEqual(4, self.finish(self.spawn(terminal_patch={
            "stop_reason": "exhausted", "exhaustion": exhausted})), self.last_result)
        self.assertEqual(3, json.loads((self.state / "status.json").read_text())["session"]["completed_steps"])

    def test_analytic_already_exhausted_does_not_spawn_with_or_without_checkpoint(self):
        for absent in (False, True):
            with self.subTest(no_checkpoint=absent):
                (self.state / "latest.pt").write_bytes(b"fixture checkpoint 123")
                self.analytic_before(exhausted=True, no_checkpoint=absent)
                self.assertEqual(4, self.finish(self.spawn()), self.last_result)
                self.assertFalse(self.child_started)

    def test_analytic_exhaustion_rejects_false_identity(self):
        self.analytic_before(exhausted=True)
        self.before["exhaustion"]["identity"] = "b" * 64
        self.save_before()
        self.assertEqual(1, self.finish(self.spawn()))
        self.assertFalse(self.child_started)

    def test_sigterm_and_sigint_forward_and_wait_for_checkpoint(self):
        for number in (signal.SIGTERM, signal.SIGINT):
            with self.subTest(number=number):
                self.save_before()
                process = self.spawn(barrier=True)
                self.event(process, "READY")
                os.kill(process.pid, number)
                self.event(process, "SIGNAL " + signal.Signals(number).name)
                self.assertIsNone(process.poll())
                self.assertEqual(128 + number, self.finish(process, release=True))
                self.assertEqual(b"fixture checkpoint 124", (self.state / "latest.pt").read_bytes())

    def test_signal_while_popen_has_created_but_not_returned_child(self):
        code = """
import os, signal, subprocess, sys
import gpu_bounded_launcher as launcher
original = subprocess.Popen
def interrupted_creation(*args, **kwargs):
    child = original(*args, stdout=subprocess.PIPE, **kwargs)
    assert child.stdout.readline().strip() == b'READY'
    print('READY', flush=True)
    os.kill(os.getpid(), signal.SIGTERM)
    original_wait = child.wait
    def wait(*args, **kwargs):
        child.wait = original_wait
        assert child.stdout.readline().strip() == b'SIGNAL SIGTERM'
        print('SIGNAL SIGTERM', flush=True)
        return original_wait(*args, **kwargs)
    child.wait = wait
    return child
subprocess.Popen = interrupted_creation
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(barrier=True, command=[sys.executable, "-c", code, str(self.state)])
        # Import uses this scratch directory; the child worker is its adjacent fixture.
        self.event(process, "READY")
        self.event(process, "SIGNAL SIGTERM")
        self.assertIsNone(process.poll())
        self.assertEqual(128 + signal.SIGTERM, self.finish(process, release=True))
        self.assertEqual(b"fixture checkpoint 124", (self.state / "latest.pt").read_bytes())

    def test_signal_after_preflight_prevents_child_creation(self):
        code = """
import os, signal, sys
import gpu_bounded_launcher as launcher
original = launcher.read_status
def interrupted_preflight(*args):
    result = original(*args)
    os.kill(os.getpid(), signal.SIGTERM)
    return result
launcher.read_status = interrupted_preflight
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(command=[sys.executable, "-c", code, str(self.state)])
        self.assertEqual(143, self.finish(process))
        self.assertFalse(self.child_started)

    def test_signal_after_success_evaluation_still_exits_nonzero(self):
        code = """
import os, signal, sys
import gpu_bounded_launcher as launcher
original = launcher.run_once
def interrupted_return(*args):
    result = original(*args)
    assert result == 0
    os.kill(os.getpid(), signal.SIGINT)
    return result
launcher.run_once = interrupted_return
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(command=[sys.executable, "-c", code, str(self.state)])
        self.assertEqual(130, self.finish(process))

    def test_signal_during_final_python_exit_still_exits_nonzero(self):
        code = """
import os, signal, sys
import gpu_bounded_launcher as launcher
result = launcher.main(['--state-dir', sys.argv[1]])
assert result == 0
os.kill(os.getpid(), signal.SIGTERM)
sys.exit(result)
"""
        process = self.spawn(command=[sys.executable, "-c", code, str(self.state)])
        self.assertEqual(143, self.finish(process))

    def test_child_only_signal_is_not_restartable(self):
        process = self.spawn(barrier=True)
        self.event(process, "READY")
        pid = json.loads((self.state / "child-started.json").read_text())["pid"]
        os.kill(pid, signal.SIGTERM)
        self.event(process, "SIGNAL SIGTERM")
        self.assertIsNone(process.poll())
        self.assertEqual(1, self.finish(process, release=True))

    def test_repeated_mixed_signals_are_forwarded_while_waiting(self):
        process = self.spawn(barrier=True)
        self.event(process, "READY")
        for number in (signal.SIGTERM, signal.SIGINT):
            os.kill(process.pid, number)
            self.event(process, "SIGNAL " + signal.Signals(number).name)
            self.assertIsNone(process.poll())
        self.assertEqual(143, self.finish(process, release=True))
        status = json.loads((self.state / "status.json").read_text())
        self.assertEqual("SIGINT", status["stop_reason"])

    def test_wait_exception_still_forwards_and_reaps_child(self):
        code = """
import subprocess, sys
import gpu_bounded_launcher as launcher
original = subprocess.Popen
def broken_wait(*args, **kwargs):
    child = original(*args, stdout=subprocess.PIPE, **kwargs)
    assert child.stdout.readline().strip() == b'READY'
    print('READY', flush=True)
    original_wait = child.wait
    def wait_once(*args, **kwargs):
        child.wait = wait_for_cleanup
        raise RuntimeError('injected wait failure')
    def wait_for_cleanup(*args, **kwargs):
        child.wait = original_wait
        assert child.stdout.readline().strip() == b'SIGNAL SIGTERM'
        print('SIGNAL SIGTERM', flush=True)
        return original_wait(*args, **kwargs)
    child.wait = wait_once
    return child
subprocess.Popen = broken_wait
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(barrier=True, command=[sys.executable, "-c", code, str(self.state)])
        self.event(process, "READY")
        self.event(process, "SIGNAL SIGTERM")
        self.assertIsNone(process.poll())
        self.assertEqual(1, self.finish(process, release=True))
        self.assertEqual(b"fixture checkpoint 124", (self.state / "latest.pt").read_bytes())

    def test_spawn_error_is_not_retried(self):
        code = """
import subprocess, sys
import gpu_bounded_launcher as launcher
def fail(*args, **kwargs):
    raise OSError('injected process creation failure')
subprocess.Popen = fail
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(command=[sys.executable, "-c", code, str(self.state)])
        self.assertEqual(1, self.finish(process))
        self.assertFalse(self.child_started)

    def test_cleanup_signal_error_cannot_skip_wait(self):
        code = """
import subprocess, sys
import gpu_bounded_launcher as launcher
original = subprocess.Popen
def broken_cleanup(*args, **kwargs):
    child = original(*args, stdout=subprocess.PIPE, **kwargs)
    assert child.stdout.readline().strip() == b'READY'
    print('READY', flush=True)
    original_wait, original_signal = child.wait, child.send_signal
    def wait_once(*args, **kwargs):
        child.wait = wait_for_cleanup
        raise RuntimeError('injected wait failure')
    def wait_for_cleanup(*args, **kwargs):
        child.wait = original_wait
        print('WAIT', flush=True)
        return original_wait(*args, **kwargs)
    def signal_error(number):
        original_signal(number)
        assert child.stdout.readline().strip() == b'SIGNAL SIGTERM'
        print('SIGNAL SIGTERM', flush=True)
        raise OSError('injected signal error after delivery')
    child.wait, child.send_signal = wait_once, signal_error
    return child
subprocess.Popen = broken_cleanup
sys.exit(launcher.main(['--state-dir', sys.argv[1]]))
"""
        process = self.spawn(barrier=True, command=[sys.executable, "-c", code, str(self.state)])
        self.event(process, "READY")
        self.event(process, "SIGNAL SIGTERM")
        self.event(process, "WAIT")
        self.assertIsNone(process.poll())
        self.assertEqual(1, self.finish(process, release=True))
        self.assertEqual(b"fixture checkpoint 124", (self.state / "latest.pt").read_bytes())


if __name__ == "__main__":
    unittest.main(verbosity=2)
