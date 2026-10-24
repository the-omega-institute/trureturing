"""Owned native commands and completed unittest fixture input disposal."""

import codecs
import json
import os
from pathlib import Path
import select
import signal
import shutil
import subprocess
import tempfile
import time
import unittest


class FixtureInterrupted(Exception):
    pass


class NativeFixture(unittest.TestCase):
    active = None

    @staticmethod
    def install_interrupt_handler():
        def interrupted(signum, frame):
            if NativeFixture.active is not None:
                NativeFixture.active.fixture_interrupted = True
            raise FixtureInterrupted("outer fixture interruption: " + str(signum))
        signal.signal(signal.SIGTERM, interrupted)
        signal.signal(signal.SIGINT, interrupted)

    def run(self, result=None):
        self.workspaces = []
        self.commands_settled = True
        self.jobs_settled = True
        self.command_serial = 0
        self.fixture_started = time.monotonic()
        self.fixture_interrupted = False
        self.cleanups_successful = False
        completed = False
        previous = NativeFixture.active
        NativeFixture.active = self
        try:
            returned = super().run(result)
            completed = True
            published_failure = any(test is self or getattr(test, "test_case", None) is self
                                    for test, _ in returned.failures + returned.errors + returned.skipped
                                    + getattr(returned, "expectedFailures", []))
            self.cleanups_successful = self.cleanups_successful and not published_failure
            return returned
        finally:
            successful = (completed and self.cleanups_successful and self.commands_settled and self.jobs_settled
                          and not self.fixture_interrupted)
            for root in self.workspaces:
                if successful:
                    shutil.rmtree(root)
                else:
                    print(json.dumps(dict(event="fixture_inputs_retained", path=str(root),
                                          commands_settled=self.commands_settled)), flush=True)
            print(json.dumps(dict(event="fixture_completion", probe=self._testMethodName,
                                  successful=successful, completed=completed,
                                  commands_settled=self.commands_settled, owned_execution_settled=self.commands_settled and self.jobs_settled,
                                  interrupted=self.fixture_interrupted,
                                  inputs=[str(p) for p in self.workspaces])), flush=True)
            NativeFixture.active = previous

    def doCleanups(self):
        # Read the aggregate outside every cleanup's testPartExecutor. This is
        # before publication on 3.9/3.10 and after publication on 3.11/3.12.
        successful = super().doCleanups()
        self.cleanups_successful = bool(self._outcome is not None and successful
                                       and not getattr(self._outcome, "skipped", []))
        return successful

    def workspace(self, prefix, directory=None):
        temporary = tempfile.TemporaryDirectory(prefix=prefix, dir=directory)
        # Automatic finalization must never erase unsuccessful/incomplete input.
        # Only the completed fixture boundary below owns disposal.
        temporary._finalizer.detach()
        root = Path(temporary.name).resolve()
        self.workspaces.append(root)
        return root

    @staticmethod
    def group_snapshot(group):
        result = subprocess.run(["ps", "-axo", "pid=,ppid=,pgid=,stat=,wchan=,command="],
                                capture_output=True, text=True, timeout=5)
        return [line.strip() for line in result.stdout.splitlines()
                if len(line.split()) >= 3 and line.split()[2] == str(group)]

    def run_owned_command(self, arguments, cwd, input=None, phase="git", timeout=120, check=True, env=None, pass_fds=()):
        arguments = list(map(str, arguments))
        cwd = str(cwd)
        if not self.commands_settled or self.fixture_interrupted:
            raise RuntimeError("earlier owned command is unsettled; inputs cannot be reused")
        self.commands_settled = False
        self.command_serial += 1
        prefix = self.root / ("native-" + str(self.command_serial))
        started = time.monotonic()
        # File-backed output lets launcher exit and pipe inheritance be independent.
        # All three streams remain owned until the native group has settled.
        with open(str(prefix) + ".stdin", "w+") as stdin, \
                open(str(prefix) + ".stdout", "w+") as stdout, \
                open(str(prefix) + ".stderr", "w+") as stderr:
            if input is not None:
                stdin.write(input)
                stdin.seek(0)
            process = subprocess.Popen(arguments, cwd=cwd, env=env,
                                       stdin=stdin, stdout=stdout, stderr=stderr,
                                       start_new_session=True, pass_fds=pass_fds)
            evidence = dict(event="fixture_command", phase=phase, command=arguments, cwd=cwd,
                            pid=process.pid, guard_seconds=timeout,
                            fixture_elapsed_seconds=started - self.fixture_started)
            print(json.dumps(dict(evidence, status="started")), flush=True)
            expired = False
            interrupted = None
            before = []
            signal_errors = []
            settlement_error = None
            offsets = [0, 0]
            decoders = [codecs.getincrementaldecoder("utf-8")(errors="replace") for _ in offsets]
            def emit_partial(final=False):
                for index, (stream, name) in enumerate(((stdout, "stdout"), (stderr, "stderr"))):
                    data = os.pread(stream.fileno(), os.fstat(stream.fileno()).st_size - offsets[index],
                                    offsets[index])
                    offsets[index] += len(data)
                    text = decoders[index].decode(data, final=final)
                    if text:
                        print(json.dumps(dict(event="fixture_command_output", phase=phase,
                                              command=arguments, pid=process.pid, stream=name,
                                              output=text, byte_offset=offsets[index],
                                              fixture_elapsed_seconds=time.monotonic() - self.fixture_started)),
                              flush=True)
            try:
                deadline = started + timeout
                last_snapshot = 0
                while process.poll() is None:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        expired = True
                        break
                    try:
                        process.wait(timeout=min(1, remaining))
                    except subprocess.TimeoutExpired:
                        pass
                    emit_partial()
                    now = time.monotonic()
                    if process.poll() is None and now - self.fixture_started >= 165 and now - last_snapshot >= 5:
                        print(json.dumps(dict(evidence, event="fixture_native_wait", status="running",
                                              elapsed_seconds=now - started,
                                              fixture_elapsed_seconds=now - self.fixture_started,
                                              native=self.group_snapshot(process.pid))), flush=True)
                        last_snapshot = now
            except BaseException as error:
                interrupted = error
            finally:
                execution_elapsed = time.monotonic() - started
                snapshot_started = time.monotonic()
                # Only this newly created process group is signalled. Other participants
                # and reused external services have independent OS lifetimes.
                try:
                    try:
                        before = self.group_snapshot(process.pid)
                    except (OSError, subprocess.SubprocessError) as error:
                        evidence["snapshot_error"] = repr(error)
                    snapshot_elapsed = time.monotonic() - snapshot_started
                    for signum in (signal.SIGTERM, signal.SIGKILL):
                        try:
                            os.killpg(process.pid, signum)
                        except ProcessLookupError:
                            break
                        except OSError as error:
                            signal_errors.append(dict(operation="signal", signal=signum, error=repr(error)))
                        until = time.monotonic() + 5
                        while time.monotonic() < until:
                            process.poll()
                            try:
                                os.killpg(process.pid, 0)
                            except ProcessLookupError:
                                break
                            except OSError as error:
                                observation = dict(operation="probe", signal=signum, error=repr(error))
                                if observation not in signal_errors:
                                    signal_errors.append(observation)
                            select.select([], [], [], 0.05)
                        else:
                            continue
                        break
                    process.poll()
                    try:
                        os.killpg(process.pid, 0)
                    except ProcessLookupError:
                        evidence["settled"] = True
                        self.commands_settled = True
                    else:
                        raise RuntimeError("owned process group survived SIGKILL")
                except BaseException as error:
                    self.commands_settled = False
                    settlement_error = repr(error)
                finally:
                    evidence["signal_errors"] = signal_errors
            settlement_elapsed = time.monotonic() - started - execution_elapsed
            emit_partial(final=True)
            stdout.seek(0)
            stderr.seek(0)
            output, errors = stdout.read(), stderr.read()
        evidence.update(status="interrupted" if interrupted else "deadline" if expired else "exited", returncode=process.returncode,
                        elapsed_seconds=time.monotonic() - started, native_before=before,
                        execution_seconds=execution_elapsed, settlement_seconds=settlement_elapsed,
                        snapshot_seconds=time.monotonic() - snapshot_started if settlement_error else snapshot_elapsed)
        if hasattr(self, "phase_commands"):
            self.phase_commands.append(dict(phase=phase, command=arguments,
                                        elapsed_seconds=evidence["elapsed_seconds"],
                                        execution_seconds=execution_elapsed,
                                        settlement_seconds=settlement_elapsed,
                                        snapshot_seconds=evidence["snapshot_seconds"]))
        if settlement_error is not None:
            evidence.update(status="unsettled", error=settlement_error, inputs_retained=str(self.root))
        print(json.dumps(evidence), flush=True)
        if settlement_error is not None:
            self.fail(json.dumps(dict(evidence, stdout=output, stderr=errors)))
        if interrupted is not None:
            raise interrupted
        if expired:
            if check:
                self.fail(json.dumps(dict(evidence, stdout=output, stderr=errors)))
            error = subprocess.TimeoutExpired(arguments, timeout, output=output, stderr=errors)
            error.lifetime = evidence
            raise error
        if check and process.returncode != 0:
            self.fail(json.dumps(dict(evidence, stdout=output, stderr=errors)))
        result = subprocess.CompletedProcess(arguments, process.returncode, output, errors)
        result.lifetime = evidence
        return result
