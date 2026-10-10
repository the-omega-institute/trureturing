"""Owned native fixture commands and completed input disposal."""

import json
import gc
import os
from pathlib import Path
import select
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from native_fixture import NativeFixture

SOURCE = Path(sys.argv.pop(1)).resolve()
SPACED = sys.argv.pop(1) == "spaced"
ENTRANCE = sys.argv.pop(1)
INVOCATION = sys.argv.pop(1)


class CommandLifetimeTests(NativeFixture):
    def mark_phase(self, phase):
        now = time.monotonic()
        if hasattr(self, "phase_started"):
            print(json.dumps(dict(event="fixture_phase", phase=self.active_phase,
                                  elapsed_seconds=now - self.phase_started,
                                  fixture_elapsed_seconds=now - self.fixture_started,
                                  commands=self.phase_commands)), flush=True)
        self.active_phase = phase
        self.phase_started = now
        self.phase_commands = []
        print(json.dumps(dict(event="fixture_phase", phase=phase, status="started",
                              fixture_elapsed_seconds=now - self.fixture_started)), flush=True)

    def run_command(self, arguments, cwd=None, input=None, phase="git"):
        return self.run_owned_command(arguments, cwd or self.repository, input, phase,
                                      timeout=120, env=self.environment)

    def setUp(self):
        self.fixture_started = time.monotonic()
        self.mark_phase("native-lifetime")
        self.commands_settled = True
        self.root = self.workspace("cleanup-lifetime-")
        self.repository = self.root
        self.environment = dict(os.environ)

    def check_lifetime(self, mode):
        material = self.root / "unrelated-input"
        material.write_text("independent material\n")
        participant = subprocess.Popen(["/bin/sh", "-c",
            'exec 3<"$1"; printf "ready\\n"; read line; cat <&3', "participant", str(material)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, start_new_session=True)
        def stop_participant():
            if participant.poll() is None:
                participant.communicate("finish\n", timeout=10)
        self.addCleanup(stop_participant)
        self.assertTrue(select.select([participant.stdout], [], [], 10)[0])
        self.assertEqual("ready\n", participant.stdout.readline())
        child_file = self.root / "child.pid"
        fifo = self.root / "ready"
        os.mkfifo(fifo)
        if mode == "normal":
            command = ['cat "$1"; printf "normal-error\\n" >&2', "native", str(material)]
        else:
            command = [
                "/bin/sh -c 'trap \"\" TERM; printf \"ready\\\\n\" > \"$1\"; exec sleep 600' "
                'child "$1" & child=$!; read ready < "$1"; '
                'printf "%s\\n" "$child" > "$2"; kill -STOP "$child"; '
                'printf "partial-output\\n"; printf "partial-error\\n" >&2; '
                + ("wait" if mode == "deadline" else "exit 7" if mode == "nonzero" else "exit 0"),
                "launcher", str(fifo), str(child_file)]
        if mode in ("nonzero", "deadline"):
            with self.assertRaises(AssertionError) as failure:
                self.run_command(["/bin/sh", "-c", *command], phase=mode)
            evidence = json.loads(str(failure.exception))
            self.assertEqual("deadline" if mode == "deadline" else "exited", evidence["status"], evidence)
            if mode == "nonzero":
                self.assertEqual(7, evidence["returncode"])
            self.assertEqual("partial-output\n", evidence["stdout"])
            self.assertEqual("partial-error\n", evidence["stderr"])
            self.assertEqual(mode, evidence["phase"])
        else:
            result = self.run_command(["/bin/sh", "-c", *command], phase=mode)
            evidence = result.lifetime
            self.assertEqual(0, result.returncode)
            self.assertEqual("independent material\n" if mode == "normal" else "partial-output\n",
                             result.stdout)
        self.assertTrue(evidence["settled"])
        with self.assertRaises(ProcessLookupError):
            os.killpg(evidence["pid"], 0)
        if mode != "normal":
            child = int(child_file.read_text())
            with self.assertRaises(ProcessLookupError):
                os.kill(child, 0)
        self.assertIsNone(participant.poll(), "independent process sharing inputs must survive")
        self.assertEqual("independent material\n", material.read_text())
        output, error = participant.communicate("finish\n", timeout=10)
        self.assertEqual(0, participant.returncode, error)
        self.assertEqual("independent material\n", output)
        print(json.dumps(dict(event="native_lifetime_assertions", mode=mode, owned_group=evidence["pid"],
                              settled=True, independent_survived=True, material_retained=True)), flush=True)

    def test_normal(self):
        self.check_lifetime("normal")

    def test_nonzero(self):
        self.check_lifetime("nonzero")

    def test_deadline(self):
        self.check_lifetime("deadline")

    def test_launcher(self):
        self.check_lifetime("launcher")


class SignalErrorTests(CommandLifetimeTests):
    def check_signal_error(self, operation):
        native_killpg = os.killpg
        injected = []
        def killpg(group, signum):
            if not injected and ((operation == "signal" and signum == signal.SIGTERM)
                                 or (operation == "probe" and signum == 0)):
                injected.append((group, signum))
                raise PermissionError(1, "injected owned-group signal/probe error")
            return native_killpg(group, signum)
        os.killpg = killpg
        try:
            self.check_lifetime("launcher")
        finally:
            os.killpg = native_killpg
        self.assertEqual(1, len(injected))
        print(json.dumps(dict(event="native_signal_error_assertions", operation=operation,
                              settled=True, independent_survived=True)), flush=True)

    def test_delivery_error(self):
        self.check_signal_error("signal")

    def test_observation_error(self):
        self.check_signal_error("probe")


class FixtureDisposalTests(NativeFixture):
    def test_completed_outcomes_and_finalizers(self):
        for publication in ("immediate", "deferred"):
            for failure in (None, "setup", "body", "subtest", "teardown", "cleanup",
                            "incomplete", "unsettled", "nested-input"):
                with self.subTest(publication=publication, failure=failure):
                    class Result(unittest.TestResult):
                        def __init__(self):
                            super().__init__()
                            self.pending = []
                        def addError(self, test, error):
                            if publication == "deferred": self.pending.append((test, error))
                            else: super().addError(test, error)
                        def stopTest(self, test):
                            for item, error in self.pending:
                                super().addError(item, error)
                            super().stopTest(test)

                    class Probe(NativeFixture):
                        def setUp(self):
                            self.root = self.workspace("fixture-disposal-")
                            (self.root / "input").write_text("recoverable input\n")
                            if failure == "nested-input":
                                self.nested = self.workspace("fixture-nested-", "/tmp")
                                (self.nested / "input").write_text("nested recovery\n")
                            def cleanup():
                                # Every supported runtime temporarily resets this flag.
                                self.assertTrue(self._outcome.success)
                                if failure == "cleanup": raise RuntimeError("cleanup failed")
                            self.addCleanup(cleanup)
                            if failure == "setup": raise RuntimeError("setup failed")
                        def test_body(self):
                            if failure == "incomplete": raise KeyboardInterrupt()
                            if failure == "unsettled": self.commands_settled = False
                            if failure == "subtest":
                                with self.subTest(): self.fail("subtest failed")
                            if failure in ("body", "nested-input"): raise RuntimeError("body failed")
                        def tearDown(self):
                            if failure == "teardown": raise RuntimeError("teardown failed")

                    probe = Probe("test_body")
                    result = Result()
                    if failure == "incomplete":
                        with self.assertRaises(KeyboardInterrupt): probe.run(result)
                    else:
                        probe.run(result)
                    paths = list(probe.workspaces)
                    del probe
                    gc.collect()
                    for path in paths:
                        self.assertEqual(failure is not None, path.exists(), str(path))
                        if path.exists():
                            self.assertIn("recovery" if failure == "nested-input" and len(paths) > 1
                                          and path == paths[1] else "recoverable", (path / "input").read_text())
                            # Dispose only the intentionally failed regression input,
                            # after verifying survival beyond fixture/GC finalization.
                            shutil.rmtree(path)
        print(json.dumps(dict(event="fixture_disposal_assertions", publication_orders=2,
                              outcomes_per_order=9, retained_after_gc=True)), flush=True)


if __name__ == "__main__":
    NativeFixture.install_interrupt_handler()
    unittest.main()
