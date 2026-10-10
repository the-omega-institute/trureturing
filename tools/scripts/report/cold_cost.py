#!/usr/bin/env python3
"""Temporary native cold-report experiment; observations never decide admission."""
import argparse
import base64
from contextlib import contextmanager
import ctypes
import functools
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import re
import selectors
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time
import zlib

SEALED_INPUTS_SHA256 = "188f08d676df9d59b9f232be65fd74576a48b744a3f089d9057ca61028b7afa0"


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def sha(path):
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256") if hasattr(hashlib, "file_digest") else None
        if digest is None:
            digest = hashlib.sha256()
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
        return digest.hexdigest()


def stamp():
    return {"monotonic_ns": time.monotonic_ns(), "realtime_ns": time.time_ns(),
            "monotonic_clock": "CLOCK_MONOTONIC", "realtime_clock": "CLOCK_REALTIME"}


def append(path, value):
    # Each compiler owns a separate file; the stage and sampler share no writer.
    with path.open("a") as stream:
        stream.write(json.dumps(value, sort_keys=True) + "\n")



TRACE_LIMIT = 64 * 1024 * 1024
# Collector diagnostics use the same bounded SignalSink as trace/live delivery.
# This per-record cap keeps an unterminated startup write inspectable without
# allowing one malformed record to consume the trace budget.
COLLECTOR_DIAGNOSTIC_LIMIT = 64 * 1024
PREFLIGHT_SECONDS = 90
TRACE_SECONDS = 180 * 60
IDENTITY_FIELDS = ("pid", "tgid", "ppid", "pgid", "sid", "start_ns", "comm")


class CommandCancelled(BaseException):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f"catchable cancellation {signum}")


_cancellation = None


@contextmanager
def cancellation_scope():
    """Latch signals without throwing across Popen's successful-spawn interval.

    The first catchable signal owns the exit status; later signals cannot
    interrupt bounded cleanup or publication. SIGKILL remains censored.
    """
    global _cancellation
    if _cancellation is not None:
        yield _cancellation
        check_cancellation()
        return
    state = {"signal": None, "terminal_cancel": None}
    def latch(signum, _frame):
        if state["signal"] is None:
            state["signal"] = signum
    previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    _cancellation = state
    try:
        for sig in previous:
            signal.signal(sig, latch)
        yield state
    finally:
        # This blocked transition is the terminal ownership point. A signal
        # latched (or pending) at entry cannot be lost on normal return. run's
        # publication consumer invalidates its receipt before ownership leaves.
        mask = signal.pthread_sigmask(signal.SIG_BLOCK, previous)
        try:
            if state["signal"] is None:
                pending = signal.sigpending().intersection(previous)
                if pending:
                    state["signal"] = min(pending)
            if sys.exc_info()[0] is None and state["signal"] is not None:
                error = CommandCancelled(state["signal"])
                if state["terminal_cancel"] is not None:
                    state["terminal_cancel"](error)
                raise error
        finally:
            if state["signal"] is not None:
                # Discard blocked repeats before restoring the caller's handlers;
                # they cannot replace the first cancellation's owned exit status.
                for sig in previous:
                    signal.signal(sig, signal.SIG_IGN)
            for sig, handler in previous.items():
                signal.signal(sig, handler)
            _cancellation = None
            signal.pthread_sigmask(signal.SIG_SETMASK, mask)


def check_cancellation():
    if _cancellation is not None and _cancellation["signal"] is not None:
        raise CommandCancelled(_cancellation["signal"])


def cancellable(function):
    @functools.wraps(function)
    def wrapped(*args, **kwargs):
        completed = False
        try:
            with cancellation_scope():
                check_cancellation()
                try:
                    value = function(*args, **kwargs)
                    completed = True
                    return value
                except BaseException as error:
                    if not isinstance(error, CommandCancelled):
                        check_cancellation()
                    raise
        except CommandCancelled as error:
            if completed:
                # run's canonical_stages consumer retains the operation's raw
                # status even when cancellation wins its normal-return handoff.
                error.command_returncode = value
            raise
    return wrapped


def _unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("ambiguous trace JSON key")
        result[key] = value
    return result


def iter_signal_records(lines, live=False, require_terminal=True):
    """Decode the ordered, checksummed deflate frames into exact retained JSON.

    Each admitted record has one immediate local/live frame. Sequence, length,
    CRC and deflate completion reject missing, reordered or corrupt frames.
    An explicitly requested prefix is evidence of that prefix only.
    """
    decoder = zlib.decompressobj()
    terminal = False
    charged = 0
    for index, line in enumerate(lines):
        if isinstance(line, bytes):
            line = line.decode("ascii")
        charged += len(line.encode("ascii")) + (0 if live else len("SIGNAL_DIAGNOSTIC "))
        if charged > TRACE_LIMIT:
            raise ValueError("trace physical live byte limit exceeded")
        if terminal or not line.endswith("\n"):
            raise ValueError("trailing or truncated trace frame")
        if live:
            if not line.startswith("SIGNAL_DIAGNOSTIC "):
                raise ValueError("unrecognized live trace frame")
            line = line[len("SIGNAL_DIAGNOSTIC "):]
        frame = json.loads(line, object_pairs_hook=_unique_json_object)
        if (not isinstance(frame, dict) or set(frame) != {"z", "n", "l", "c"}
                or type(frame["n"]) is not int or frame["n"] != index
                or type(frame["l"]) is not int or not 0 < frame["l"] <= TRACE_LIMIT
                or not isinstance(frame["z"], str) or not isinstance(frame["c"], str)
                or re.fullmatch(r"[0-9a-f]{8}", frame["c"]) is None):
            raise ValueError("ambiguous trace frame schema or sequence")
        try:
            compressed = base64.b64decode(frame["z"], validate=True)
            if base64.b64encode(compressed).decode("ascii") != frame["z"]:
                raise ValueError("noncanonical trace base64")
            raw = decoder.decompress(compressed, frame["l"] + 1)
        except (ValueError, zlib.error) as error:
            raise ValueError("invalid trace deflate frame") from error
        if (len(raw) != frame["l"] or decoder.unconsumed_tail or decoder.unused_data
                or f"{zlib.crc32(raw):08x}" != frame["c"]):
            raise ValueError("trace frame length or checksum mismatch")
        record = json.loads(raw, object_pairs_hook=_unique_json_object)
        if not isinstance(record, dict) or not isinstance(record.get("kind"), str):
            raise ValueError("trace payload is not a record")
        terminal = record["kind"] == "trace-terminal"
        if terminal != decoder.eof:
            raise ValueError("trace terminal and deflate completion mismatch")
        if not terminal and not compressed.endswith(b"\x00\x00\xff\xff"):
            raise ValueError("truncated trace deflate flush boundary")
        # Kernel-record validation is shared with fixture attribution; metadata
        # remains exactly the original JSON value, without a selected domain.
        decode_signal_record(record)
        yield record
    if require_terminal and not terminal:
        raise ValueError("trace terminal absent; retention is censored")


def validate_retained_trace(path, require_healthy=True):
    """The artifact/health consumer checks the actual retained encoding."""
    with path.open("rb") as stream:
        terminal = None
        for terminal in iter_signal_records(stream):
            pass
    if require_healthy:
        require_trace_health(terminal)
    return terminal


class LinuxObservation:
    """Bounded diagnostic snapshots, independent of the raw stream's lock/FD.

    Phase spans are inclusive wall intervals, not exact CPU attribution. Proc
    snapshots bracket reads and retain tick uncertainty; missing data stays
    unavailable. Accepted console bytes do not certify hosted retention.
    """
    def __init__(self, output, interval=2.0, limit=8 * 1024 * 1024, proc=Path("/proc")):
        self.output, self.interval, self.limit, self.proc = output, interval, limit, proc
        self.active, self.totals, self.counters = {}, {}, {}
        self.state_lock = threading.Lock()
        self.done = threading.Event()
        self.thread = None
        self.receiver_tid = None
        self.collector_pid = None
        self.sink = None
        self.pipes = {}
        self.snapshot_sequence = self.journal_bytes = 0
        self.journal_capped = False
        self.persistence_error = None
        self.observer_tid = None
        self.started_ns = time.monotonic_ns()
        self.last_snapshot_ns = None
        self.max_gap_ns = 0
        self.observation_cpu_ns = self.observation_wall_ns = 0
        self.persist_wall_ns = 0
        self.persisted_bytes = 0
        self.calls = 0
        self.owners = {}
        self.system_forks_observed = self.fork_tracking_capped = 0

    def add(self, name, value=1):
        with self.state_lock:
            self.counters[name] = self.counters.get(name, 0) + value

    def set(self, name, value):
        with self.state_lock:
            self.counters[name] = value

    @contextmanager
    def span(self, phase):
        tid, started = threading.get_native_id(), time.monotonic_ns()
        with self.state_lock:
            self.calls += 1
            generation = self.calls
            previous = self.active.get(tid)
            self.active[tid] = {"phase": phase, "generation": generation, "start_monotonic_ns": started}
            total = self.totals.setdefault(phase, {"calls": 0, "completed": 0, "errors": 0, "elapsed_ns": 0})
            total["calls"] += 1
        failed = False
        try:
            yield
        except BaseException:
            failed = True
            raise
        finally:
            with self.state_lock:
                total["errors" if failed else "completed"] += 1
                total["elapsed_ns"] += time.monotonic_ns() - started
                if previous is None: self.active.pop(tid, None)
                else: self.active[tid] = previous

    def register_owner(self, role, pid, start_ticks, hz):
        key = (role, pid, start_ticks)
        with self.state_lock:
            if key not in self.owners:
                if len(self.owners) >= 128:
                    self.fork_tracking_capped += 1
                    return
                self.owners[key] = {"role": role, "pid": pid, "start_ticks": start_ticks,
                    "hz": hz, "registered_monotonic_ns": time.monotonic_ns(),
                    "direct_observed": 0, "descendant_observed": 0, "live_descendants": set()}

    def observe_event(self, event):
        if event["kind"] not in ("fork", "exit"): return
        actor = (event["actor"]["pid"], event["actor"]["start_ns"])
        with self.state_lock:
            if event["kind"] == "fork": self.system_forks_observed += 1
            for owner in self.owners.values():
                direct = actor[0] == owner["pid"] and actor[1] * owner["hz"] // 1000000000 == owner["start_ticks"]
                descendant = actor in owner["live_descendants"]
                if event["kind"] == "exit":
                    owner["live_descendants"].discard(actor)
                elif direct or descendant:
                    owner["direct_observed" if direct else "descendant_observed"] += 1
                    child = (event["child"]["pid"], event["child"]["start_ns"])
                    if len(owner["live_descendants"]) < 4096: owner["live_descendants"].add(child)
                    else: self.fork_tracking_capped += 1

    def fork_snapshot(self):
        with self.state_lock:
            return {"system_forks_observed": self.system_forks_observed,
                    "tracking_capped": self.fork_tracking_capped,
                    "scope": "since owner registration; missing/lost/earlier events are not reconstructed",
                    "phase_attribution": "unavailable; delayed delivery and quantized owner boundaries",
                    "identity_uncertainty": "direct matches boot-tick interval; descendants use exact kernel PID/start_ns",
                    "owners": [{k: v for k, v in owner.items() if k != "live_descendants"}
                               for owner in self.owners.values()]}

    def task_snapshot(self, pid, tid=None):
        started = time.monotonic_ns()
        path = self.proc / str(pid)
        if tid is not None: path = path / "task" / str(tid)
        result = {"pid": pid, "tid": tid, "collection_start_monotonic_ns": started,
                  "identity_start_clock": "boot-ticks; interval uncertainty one clock tick"}
        try:
            def fields():
                text = (path / "stat").read_text()
                return text[text.rfind(")") + 2:].split()
            f = fields()
            hz = os.sysconf("SC_CLK_TCK")
            result.update(status="observed", start_ticks=int(f[19]), state=f[0], ppid=int(f[1]),
                          user_ticks=int(f[11]), system_ticks=int(f[12]), clock_ticks_per_second=hz,
                          start_ns_lower=int(f[19]) * 1000000000 // hz,
                          start_uncertainty_ns=(1000000000 + hz - 1) // hz)
            for name in ("schedstat", "io", "wchan", "status"):
                try:
                    raw = (path / name).read_text()
                    if name == "schedstat":
                        values = [int(x) for x in raw.split()[:3]]
                        if len(values) != 3: raise ValueError("schedstat schema")
                        result[name] = {"runtime_ns": values[0], "runqueue_wait_ns": values[1], "timeslices": values[2],
                                        "availability": "zero counters do not establish enabled accounting"}
                    elif name == "status":
                        result["context_switches"] = {line.split(":", 1)[0]: int(line.split(":", 1)[1])
                            for line in raw.splitlines() if line.startswith(("voluntary_ctxt_switches:", "nonvoluntary_ctxt_switches:"))}
                    else: result[name] = raw.strip()
                except (OSError, ValueError) as error:
                    result[name] = {"status": "unavailable", "error": type(error).__name__}
            if int(fields()[19]) != result["start_ticks"]:
                result = {"pid": pid, "tid": tid, "status": "unavailable", "error": "identity-changed"}
        except (OSError, ValueError, IndexError) as error:
            result.update(status="unavailable", error=type(error).__name__)
        result["collection_elapsed_ns"] = time.monotonic_ns() - started
        return result

    def fd_snapshot(self, fd):
        import stat
        result = {"fd": fd}
        try:
            st = os.fstat(fd)
            kind = "pipe" if stat.S_ISFIFO(st.st_mode) else "file" if stat.S_ISREG(st.st_mode) else "other"
            result.update(status="observed", type=kind, inode=st.st_ino, device=st.st_dev, size=st.st_size)
            if kind == "pipe":
                import array, fcntl, termios
                try:
                    count = array.array("i", [0])
                    fcntl.ioctl(fd, termios.FIONREAD, count, True)
                    result["unread_bytes"] = count[0]
                except (OSError, AttributeError) as error:
                    result["unread_bytes"] = {"status": "unavailable", "error": type(error).__name__}
                try: result["capacity_bytes"] = fcntl.fcntl(fd, fcntl.F_GETPIPE_SZ)
                except (OSError, AttributeError) as error:
                    result["capacity_bytes"] = {"status": "unavailable", "error": type(error).__name__}
        except (OSError, ValueError) as error:
            result.update(status="unavailable", error=type(error).__name__)
        return result

    def snapshot(self):
        begin = time.monotonic_ns()
        row = {**stamp(), "schema": 1, "snapshot_sequence": self.snapshot_sequence,
               "cadence_seconds": self.interval, "max_gap_ns": self.max_gap_ns,
               "journal_limit_bytes": self.limit, "journal_bytes": self.journal_bytes,
               "journal_capped": self.journal_capped, "persistence_error": self.persistence_error,
               "observation_cpu_ns": self.observation_cpu_ns, "observation_wall_ns": self.observation_wall_ns,
               "persist_wall_ns": self.persist_wall_ns, "persisted_bytes": self.persisted_bytes,
               "new_observer_process_forks": 0, "observer_threads": 1 if self.thread else 0,
               "fork_metric_scope": "kernel task-fork stream includes thread creation; counts below are observed",
               "boundary_calls": self.calls, "boundary_clock_reads": 2 * self.calls,
               "overhead_scope": "snapshot thread CPU/wall/bytes; hot-path overhead and uninstrumented counterfactual unverified",
               "phase_attribution": "periodic inclusive spans; boundaries may miss short calls; not causal",
               "clock_resolution_ns": {name: int(time.get_clock_info(name).resolution * 1e9)
                                         for name in ("monotonic", "time", "thread_time")}}
        try:
            row["boottime_ns"] = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
            row["boottime_resolution_ns"] = int(time.clock_getres(time.CLOCK_BOOTTIME) * 1e9)
        except (OSError, AttributeError) as error:
            row["boottime_ns"] = {"status": "unavailable", "error": type(error).__name__}
        with self.state_lock:
            row.update(active={str(k): dict(v) for k, v in self.active.items()},
                       totals={k: dict(v) for k, v in self.totals.items()}, counters=dict(self.counters))
        row["tasks"] = {"observer": self.task_snapshot(os.getpid(), self.observer_tid),
                        "receiver": self.task_snapshot(os.getpid(), self.receiver_tid) if self.receiver_tid else {"status": "unavailable", "error": "receiver-not-started"},
                        "collector": self.task_snapshot(self.collector_pid) if self.collector_pid else {"status": "unavailable", "error": "collector-not-started"}}
        row["pipes"] = {name: self.fd_snapshot(fd) for name, fd in list(self.pipes.items())}
        for role, task in row["tasks"].items():
            if task.get("status") == "observed":
                self.register_owner(role, task.get("tid") or task["pid"], task["start_ticks"], task["clock_ticks_per_second"])
        row["fork_totals"] = self.fork_snapshot()
        row["host"] = {}
        for name in ("stat", "loadavg", "pressure/cpu", "pressure/io"):
            try:
                raw = (self.proc / name).read_text()
                row["host"][name] = {"raw": raw[:8192], "truncated": len(raw) > 8192}
            except OSError as error: row["host"][name] = {"status": "unavailable", "error": type(error).__name__}
        row["collector_identity_scope"] = "Popen launch PID; sudo/provider descendants are separately observed"
        row["collector_children"] = []
        if self.collector_pid:
            try:
                ids = (self.proc / str(self.collector_pid) / "task" / str(self.collector_pid) / "children").read_text().split()
                row["collector_children"] = [self.task_snapshot(int(pid)) for pid in ids[:32]]
                row["collector_children_omitted"] = max(0, len(ids) - 32)
            except (OSError, ValueError) as error:
                row["collector_children"] = {"status": "unavailable", "error": type(error).__name__}
        shell = []
        for path in sorted(self.output.glob("shell-*.metrics"))[:256]:
            try:
                raw = path.read_bytes()
                if len(raw) > 2048 or not raw.endswith(b"\n") or raw != path.read_bytes():
                    shell.append({"file": path.name, "status": "unavailable", "error": "partial-or-changing-receipt"})
                else:
                    receipt = raw.decode("ascii")
                    shell.append({"file": path.name, "receipt": receipt})
                    fields = dict(item.split("=", 1) for item in receipt.split() if "=" in item)
                    if fields.get("pid", "").isdigit() and fields.get("start_ticks", "").isdigit():
                        self.register_owner(fields["owner"], int(fields["pid"]), int(fields["start_ticks"]), os.sysconf("SC_CLK_TCK"))
            except (OSError, UnicodeError) as error:
                shell.append({"file": path.name, "status": "unavailable", "error": type(error).__name__})
        # Shell receipts have their own bounded slots; journal snapshots carry
        # at most eight receipts by slot name and explicitly count omission.
        row["shell_receipts"] = shell[-8:]
        row["shell_receipts_omitted"] = max(0, len(shell) - 8)
        if self.sink:
            row["sink"] = {"sequence": self.sink.sequence, "charged_live_bytes": self.sink.bytes,
                           "drops": self.sink.dropped_events, "console_error": self.sink.console_error,
                           "retention_error": self.sink.retention_error}
            try: row["sink"]["file_bytes"] = self.sink.path.stat().st_size
            except OSError as error: row["sink"]["file_bytes"] = {"status": "unavailable", "error": type(error).__name__}
            try: row["console"] = self.fd_snapshot(self.sink.console.fileno())
            except (OSError, ValueError, AttributeError) as error: row["console"] = {"status": "unavailable", "error": type(error).__name__}
        row["collection_start_monotonic_ns"] = begin
        row["collection_elapsed_ns"] = time.monotonic_ns() - begin
        return row

    def persist(self):
        started, cpu = time.monotonic_ns(), time.thread_time_ns()
        self.snapshot_sequence += 1
        if self.last_snapshot_ns is not None:
            self.max_gap_ns = max(self.max_gap_ns, started - self.last_snapshot_ns)
        self.last_snapshot_ns = started
        try:
            data = (json.dumps(self.snapshot(), separators=(",", ":"), sort_keys=True) + "\n").encode()
            # Latest snapshot survives the journal cap; neither path is the
            # console or trace file under observation. Each snapshot is bounded.
            if len(data) > 65536: raise ValueError("metrics snapshot exceeds 64KiB")
            tmp = self.output / "observation-latest.json.tmp"
            tmp.write_bytes(data)
            os.replace(tmp, self.output / "observation-latest.json")
            self.persisted_bytes += len(data)
            if self.journal_bytes + len(data) <= self.limit:
                with (self.output / "observation.jsonl").open("ab") as stream: stream.write(data)
                self.journal_bytes += len(data)
                self.persisted_bytes += len(data)
            else: self.journal_capped = True
        except (OSError, ValueError) as error:
            self.persistence_error = type(error).__name__
        finally:
            self.observation_cpu_ns += time.thread_time_ns() - cpu
            self.observation_wall_ns += time.monotonic_ns() - started
            self.persist_wall_ns += time.monotonic_ns() - started

    def start(self):
        def observe():
            self.observer_tid = threading.get_native_id()
            while not self.done.is_set():
                self.persist()
                self.done.wait(self.interval)
            self.persist()
        self.thread = threading.Thread(target=observe, name="cold-cost-observation", daemon=True)
        self.thread.start()
        return self

    def stop(self):
        self.done.set()
        if self.thread: self.thread.join(timeout=1)
        if self.thread and self.thread.is_alive(): self.persistence_error = "metrics-thread-did-not-finish"
        return {"persistence_error": self.persistence_error, "journal_capped": self.journal_capped,
                "journal_bytes": self.journal_bytes, "persisted_bytes": self.persisted_bytes,
                "observation_cpu_ns": self.observation_cpu_ns, "observation_wall_ns": self.observation_wall_ns}


@contextmanager
def observation_span(observation, phase):
    if observation is None:
        yield
    else:
        with observation.span(phase): yield


def observed_phase(phase):
    def decorate(function):
        @functools.wraps(function)
        def call(self, *args, **kwargs):
            with observation_span(getattr(self, "observation", None), phase):
                return function(self, *args, **kwargs)
        return call
    return decorate


class SignalSink:
    """One bounded evidence stream, mirrored live with bounded delivery.

    Missing terminal record means retention is censored; after-steps are optional.
    Console delivery beyond the runner's last retained line is never certified.
    """
    def __init__(self, path, console=None, limit=TRACE_LIMIT, observation=None):
        self.observation = observation
        self.path = path
        self.stream = path.open("w", buffering=1)
        self.console = sys.stdout if console is None else console
        self.limit = limit
        self.reserve = min(4096, limit // 2)
        self.bytes = 0
        self.dropped_events = 0
        self.retention_error = None
        self.console_error = None
        self.lock = threading.Lock()
        self.closed = False
        self.encoder = zlib.compressobj()
        self.sequence = 0

    @observed_phase("encode")
    def _encode(self, event, terminal):
        raw = json.dumps(event, sort_keys=True).encode()
        encoder = self.encoder.copy()
        compressed = encoder.compress(raw) + encoder.flush(zlib.Z_FINISH if terminal else zlib.Z_SYNC_FLUSH)
        frame = {"z": base64.b64encode(compressed).decode("ascii"), "n": self.sequence,
                 "l": len(raw), "c": f"{zlib.crc32(raw):08x}"}
        return json.dumps(frame, separators=(",", ":")) + "\n", encoder

    def _terminal_event(self, event):
        drops = max(event.get("dropped_events", 0), self.dropped_events)
        return dict(event, dropped_events=drops,
                    retention="censored" if drops or event.get("retention") == "censored"
                    else "local-terminal-collected")

    @observed_phase("console-delivery")
    def _deliver(self, text):
        # emit/finish serve the required trace-health consumer (GoalArtifact
        # canonical-report/integration evidence). Never hold its lifecycle lock
        # across a blocking live-console write or buffered flush. Memory-only
        # fixture consoles have no external reader; other streams need an fd.
        if self.console_error is not None:
            self.dropped_events += 1
            return
        if self.observation: self.observation.add("console_attempted_bytes", len(text.encode()))
        try:
            if isinstance(self.console, io.StringIO):
                self.console.write(text)
                if self.observation: self.observation.add("console_write_bytes", len(text.encode()))
                return
            fd = self.console.fileno()
            blocking = os.get_blocking(fd)
            try:
                os.set_blocking(fd, False)
                data = memoryview(text.encode())
                deadline = time.monotonic() + .25
                while data:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise TimeoutError("live-console-backpressure")
                    try:
                        with observation_span(self.observation, "console-write"):
                            written = os.write(fd, data)
                        if self.observation:
                            self.observation.add("console_write_bytes", written)
                            self.observation.add("console_writes")
                            if written < len(data): self.observation.add("console_partial_writes")
                        if written == 0:
                            raise OSError("live-console-zero-write")
                        data = data[written:]
                    except BlockingIOError:
                        # select also supports redirected regular-file stdout.
                        if self.observation: self.observation.add("console_eagain")
                        with observation_span(self.observation, "console-writability-wait"):
                            __import__("select").select([], [fd], [], remaining)
            finally:
                os.set_blocking(fd, blocking)
        except (OSError, ValueError, TypeError, AttributeError) as error:
            self.console_error = type(error).__name__
            self.dropped_events += 1

    def emit(self, event, terminal=False):
        with observation_span(self.observation, "emit-lock"):
            self.lock.acquire()
        try:
            if self.closed:
                return
            if terminal:
                event = self._terminal_event(event)
            record, encoder = self._encode(event, terminal)
            text = "SIGNAL_DIAGNOSTIC " + record
            size = len(text.encode())
            if self.bytes + size > self.limit - (0 if terminal else self.reserve):
                self.dropped_events += 1
                return
            # Charge admitted live bytes before either output can fail. Partial
            # console delivery and local write/flush loss cannot reuse budget.
            self.bytes += size
            self._deliver(text)
            if terminal:
                event = self._terminal_event(event)
                record, encoder = self._encode(event, terminal)
                extra = max(0, len(("SIGNAL_DIAGNOSTIC " + record).encode()) - size)
                if self.bytes + extra > self.limit:
                    self.dropped_events += 1
                    return
                self.bytes += extra
            self.encoder = encoder
            self.sequence += 1
            try:
                if self.observation: self.observation.add("trace_attempted_bytes", len(record.encode()))
                with observation_span(self.observation, "trace-write"):
                    written = self.stream.write(record)
                if self.observation:
                    if type(written) is int: self.observation.add("trace_write_bytes", written)
                    else: self.observation.add("trace_write_count_unavailable")
                with observation_span(self.observation, "trace-flush"):
                    self.stream.flush()
                if self.observation: self.observation.add("trace_flush_completed")
            except OSError as error:
                self.dropped_events += 1
                self.retention_error = type(error).__name__
                return

        finally:
            self.lock.release()

    @observed_phase("finish")
    def finish(self, health):
        self.emit({"kind": "trace-terminal", **health,
                   "console_retention": "only actually retained live lines are evidence"}, terminal=True)
        with self.lock:
            self.closed = True
            try:
                self.stream.close()
            except OSError as error:
                self.dropped_events += 1
                self.retention_error = type(error).__name__
        try:
            validate_retained_trace(self.path, require_healthy=False)
        except (OSError, ValueError) as error:
            self.dropped_events += 1
            self.retention_error = self.retention_error or type(error).__name__


def _wire_identity(fields):
    if len(fields) != 7:
        raise ValueError("identity schema mismatch")
    values = [int(v) for v in fields[:6]]
    if any(v < 0 for v in values):
        raise ValueError("negative identity field")
    # comm is a kernel task basename, never argv, environment or executable path.
    return dict(zip(IDENTITY_FIELDS, values + [re.sub(r"[^A-Za-z0-9_.-]", "_", fields[6])[:16]]))


def parse_signal_wire(line):
    f = line.rstrip("\n").split("\t")
    if f == ["D", "ready"]:
        return {"kind": "trace-ready"}
    if len(f) < 3 or f[0] != "D":
        raise ValueError("unrecognized event schema")
    kind, now = f[1], int(f[2])
    row = {"kind": kind, "boottime_ns": now, "event_clock": "CLOCK_BOOTTIME",
           "identity_start_clock": "boot-nanoseconds"}
    if kind == "signal" and len(f) == 22:
        row.update(zip(("signal", "errno", "code", "group", "result"), map(int, f[3:8])))
        row.update(sender=_wire_identity(f[8:15]), target=_wire_identity(f[15:22]))
    elif kind == "delivery" and len(f) == 13:
        row.update(zip(("signal", "errno", "code"), map(int, f[3:6])))
        row["target"] = _wire_identity(f[6:13])
    elif kind in ("fork", "exit") and len(f) == (17 if kind == "fork" else 11):
        row["actor"] = _wire_identity(f[3:10])
        if kind == "fork":
            row["child"] = _wire_identity(f[10:17])
        else:
            row["kernel_exit_code"] = int(f[10])
    elif kind == "oom-victim" and len(f) == 11:
        row["victim_pid"] = int(f[3])
        row["actor"] = _wire_identity(f[4:11])
        row["victim_identity_limit"] = "kernel victim PID; start identity requires corroborating signal/fork/snapshot event"
    elif kind in ("kill", "tkill", "tgkill", "pidfd_send_signal") and len(f) == 14:
        row.update(zip(("signal", "requested_target", "requested_tgid", "flags"), map(int, f[3:7])))
        row["sender"] = _wire_identity(f[7:14])
    else:
        raise ValueError("event field count mismatch")
    return row


def decode_signal_record(record):
    """Expand a self-contained retained wire record for evidence consumers.

    The existing wire parser supplies the clocks and complete task identities.
    Legacy expanded events and non-kernel records retain their original shape.
    """
    if "wire" not in record:
        return record
    if set(record) != {"kind", "wire"} or not isinstance(record["wire"], str):
        raise ValueError("ambiguous retained signal record")
    event = parse_signal_wire(record["wire"])
    if event["kind"] != record["kind"]:
        raise ValueError("retained signal kind mismatch")
    return event


def require_trace_health(health):
    required = {"ready", "lost_events", "dropped_events", "parse_errors", "reader_error", "collector_returncode"}
    if (not required <= health.keys() or not health.get("ready") or any(health.get(k, 0) for k in
            ("lost_events", "dropped_events", "parse_errors")) or health.get("reader_error")
            or health.get("retention_error") or health.get("console_error")
            or health.get("retention") == "censored"
            or health.get("collector_returncode") not in (None, 0)):
        raise ValueError("signal capability absent, ambiguous, lost or censored; workload is forbidden")


class TraceHealthError(ValueError):
    def __init__(self, reason, health):
        super().__init__(reason)
        self.reason, self.health = reason, health


def signal_program(seconds):
    # BTF resolves these kernel fields at actual hosted compilation. No offsets
    # are guessed; unsupported schemas fail capability preflight.
    def ident(v):
        return ", ".join((f"{v}->pid", f"{v}->tgid", f"{v}->real_parent->tgid",
                          f"{v}->signal->pids[2]->numbers[0].nr",
                          f"{v}->signal->pids[3]->numbers[0].nr", f"{v}->start_boottime", f"str({v}->comm)"))
    fmt = "%d\\t%d\\t%d\\t%d\\t%d\\t%llu\\t%s"
    probes = [f'BEGIN {{ @deadline = nsecs + {int(seconds)} * 1000000000; printf("D\\tready\\n"); }}',
              'interval:s:1 { if (nsecs > @deadline) { exit(); } }',
              'END { clear(@deadline); }']
    probes.append('rawtracepoint:signal_generate { $s = curtask; '
                  '$t = (struct task_struct *)arg2; $i = (struct kernel_siginfo *)arg1; '
                  f'printf("D\\tsignal\\t%llu\\t%d\\t%d\\t%d\\t%d\\t%d\\t{fmt}\\t{fmt}\\n", '
                  f'nsecs, arg0, (arg1 > 1 ? $i->si_errno : 0), (arg1 == 1 ? 128 : (arg1 == 0 ? 0 : $i->si_code)), arg3, arg4, {ident("$s")}, {ident("$t")}); }}')
    probes.append('rawtracepoint:sched_process_fork { $s = (struct task_struct *)arg0; '
                  '$t = (struct task_struct *)arg1; '
                  f'printf("D\\tfork\\t%llu\\t{fmt}\\t{fmt}\\n", nsecs, {ident("$s")}, {ident("$t")}); }}')
    probes.append('rawtracepoint:signal_deliver { $t = curtask; '
                  '$i = (struct kernel_siginfo *)arg1; '
                  f'printf("D\\tdelivery\\t%llu\\t%d\\t%d\\t%d\\t{fmt}\\n", '
                  f'nsecs, arg0, $i->si_errno, $i->si_code, {ident("$t")}); }}')
    probes.append('rawtracepoint:sched_process_exit { $t = (struct task_struct *)arg0; '
                  f'printf("D\\texit\\t%llu\\t{fmt}\\t%d\\n", nsecs, {ident("$t")}, $t->exit_code); }}')
    probes.append('tracepoint:oom:mark_victim { $s = curtask; '
                  f'printf("D\\toom-victim\\t%llu\\t%d\\t{fmt}\\n", nsecs, args->pid, {ident("$s")}); }}')
    for kind, target, tgid, flags in (("kill", "args->pid", "0", "0"),
            ("tkill", "args->pid", "0", "0"), ("tgkill", "args->pid", "args->tgid", "0"),
            ("pidfd_send_signal", "args->pidfd", "0", "args->flags")):
        probes.append(f'tracepoint:syscalls:sys_enter_{kind} {{ $s = curtask; '
                      f'printf("D\\t{kind}\\t%llu\\t%d\\t%d\\t%d\\t%d\\t{fmt}\\n", '
                      f'nsecs, args->sig, {target}, {tgid}, {flags}, {ident("$s")}); }}')
    return "\n".join(probes)


class SignalTrace:
    """Passive system-wide kernel events; only this owned tracer is stopped.

    Process start identities come from the event's task_struct, avoiding /proc
    races for short-lived senders/targets. System-wide collection is needed for
    external actors. Event wire contains task basenames and numeric fields;
    collector failure diagnostics retain bounded original bytes separately.
    """
    def __init__(self, output, seconds=TRACE_SECONDS, observation=None):
        self.observation = observation
        self.output, self.seconds = output, seconds
        self.ready = threading.Event()
        self.health = {"ready": False, "lost_events": 0, "parse_errors": 0, "reader_error": None}
        self.events = []  # Only fixture evidence is kept in memory, never workload events.
        self.fixture = False
        self.process = None
        self.sink = None
        self.thread = None
        self.deadline = None

    def start(self):
        if platform.system() != "Linux" or not Path("/sys/kernel/btf/vmlinux").is_file():
            raise ValueError("Linux kernel BTF capability unavailable")
        tool = shutil.which("bpftrace")
        if tool is None:
            raise ValueError("bpftrace unavailable")
        prefix = [] if os.geteuid() == 0 else ["sudo", "-n"]
        self.sink = SignalSink(self.output / "signal-trace.jsonl", observation=self.observation)
        if self.observation: self.observation.sink = self.sink
        self.sink.emit({"kind": "trace-contract", "seconds": self.seconds, "limit_bytes": TRACE_LIMIT,
                       "limit_scope": "trace file/live stream; not aggregate artifacts",
                       "kernel_event_clock": "bpftrace default nsecs: CLOCK_BOOTTIME",
                       "python_stamp_clock": "CLOCK_MONOTONIC; realtime separately CLOCK_REALTIME",
                       "identity_start_clock": "task_struct.start_boottime; boot-nanoseconds",
                       "ordering": "collector arrival; no global cross-CPU causal order",
                       "event_scope": "system-wide signal generation/delivery, fork, exit, signal syscalls and OOM victim",
                       "kernel_record_encoding": "JSON kind/wire; decode_signal_record restores parse_signal_wire fields; each record is self-contained",
                       "limitations": "no IPC contents, actor motive, provider identity or historical events; absent terminal is censored",
                       "clock_ticks_per_second": os.sysconf("SC_CLK_TCK")})
        try:
            self.deadline = time.monotonic() + self.seconds
            # The bundled AppRun needs mount privileges in both launch scopes.
            version = self._provider_version(prefix + [tool, "--version"])
            self.sink.emit({"kind": "kernel-capability-binding", "kernel_release": platform.release(),
                           "bpftrace_version": re.sub(r"[^A-Za-z0-9_. -]", "_", version.strip())[:80],
                           "program_sha256": hashlib.sha256(signal_program(self.seconds).encode()).hexdigest(),
                           "BTF": "present; kernel fields resolved by actual attachment", "privilege": "root" if not prefix else "sudo-n",
                           "required_probes": ["signal_generate", "signal_deliver", "sched_process_fork", "sched_process_exit", "mark_victim",
                                               "sys_enter_kill", "sys_enter_tkill", "sys_enter_tgkill", "sys_enter_pidfd_send_signal"],
                           "OOM_validation": "attachment only; no OOM is induced"})
            self.process = subprocess.Popen(prefix + [tool, "-q", "-B", "line", "-e", signal_program(self.seconds)],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    env={"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "BPFTRACE_PERF_RB_PAGES": "64"})
            self.thread = threading.Thread(target=self._read)
            self.thread.start()
            if not self.ready.wait(20):
                raise ValueError("kernel trace did not become ready within 20 seconds")
            self.check()
        except BaseException:
            self.stop()
            raise
        return self

    def _provider_version(self, command):
        try:
            result = subprocess.run(command, capture_output=True, timeout=5, check=False)
        except subprocess.TimeoutExpired as error:
            self._record_provider_version(command, None, error.stdout, error.stderr, "timeout")
            raise
        except OSError as error:
            self._record_provider_version(command, None, None, None, "launch-error",
                                          error=type(error).__name__, errno=error.errno)
            raise
        self._record_provider_version(command, result.returncode, result.stdout, result.stderr, "completed")
        result.check_returncode()
        return result.stdout.decode(errors="replace")

    def _record_provider_version(self, command, returncode, stdout, stderr, outcome, **failure):
        streams = {}
        for name, raw in (("stdout", stdout), ("stderr", stderr)):
            raw = raw or b""
            retained = raw[:COLLECTOR_DIAGNOSTIC_LIMIT]
            truncated = len(raw) > len(retained)
            if truncated:
                with self.sink.lock:
                    self.sink.dropped_events += 1
            streams[name] = {"raw_bytes_base64": base64.b64encode(retained).decode("ascii"),
                             "raw_sha256": hashlib.sha256(retained).hexdigest(),
                             "raw_byte_length": len(retained), "observed_byte_length": len(raw),
                             "truncated": truncated, "encoding": "base64"}
        self.sink.emit({"kind": "provider-version", "command": command,
                        "returncode": returncode, "outcome": outcome, **streams, **failure})

    def _read(self):
        if self.observation:
            self.observation.receiver_tid = threading.get_native_id()
            self.observation.collector_pid = self.process.pid
            self.observation.pipes = {"stdout": self.process.stdout.fileno(), "stderr": self.process.stderr.fileno()}
        sel = selectors.DefaultSelector()
        buffers = {}
        streams = ((self.process.stdout, "stdout"), (self.process.stderr, "stderr"))
        for pipe, stream in streams:
            os.set_blocking(pipe.fileno(), False)
            sel.register(pipe, selectors.EVENT_READ)
            buffers[pipe] = (stream, b"", False)
        try:
            while sel.get_map():
                if time.monotonic() > self.deadline + 5:
                    self.health["reader_error"] = "collector-deadline"
                    self.process.kill()
                with observation_span(self.observation, "selector-wait"):
                    selected = sel.select(timeout=1)
                for key, _ in selected:
                    with observation_span(self.observation, "pipe-read"):
                        block = os.read(key.fileobj.fileno(), 65536)
                    if self.observation:
                        self.observation.add("pipe_reads")
                        self.observation.add("pipe_read_bytes", len(block))
                    stream, buffered, continuation = buffers[key.fileobj]
                    if not block:
                        if buffered:
                            self.health["parse_errors"] += 1
                            self._record_collector_diagnostic(stream, buffered,
                                                              reason="eof-partial-output",
                                                              terminated=False)
                        sel.unregister(key.fileobj)
                        continue
                    buffered += block
                    if self.observation: self.observation.set("input_buffer_bytes", len(buffered) + sum(len(v[1]) for k, v in buffers.items() if k is not key.fileobj))
                    while b"\n" in buffered:
                        line, buffered = buffered.split(b"\n", 1)
                        if continuation:
                            self._record_collector_diagnostic(
                                stream, line, reason="oversized-output-continuation")
                        else:
                            self._line(line.decode(errors="replace"), stream=stream,
                                       raw=line, terminated=True)
                        continuation = False
                    if len(buffered) > COLLECTOR_DIAGNOSTIC_LIMIT:
                        self.health["parse_errors"] += 1
                        self._record_collector_diagnostic(
                            stream, buffered,
                            reason="oversized-unterminated-output", terminated=False,
                            truncated=True)
                        buffered = b""
                        continuation = True
                    buffers[key.fileobj] = (stream, buffered, continuation)
                    if self.observation: self.observation.set("input_buffer_bytes", sum(len(v[1]) for v in buffers.values()))
        except BaseException as error:
            self.health["reader_error"] = type(error).__name__
        finally:
            sel.close()

    def _record_collector_diagnostic(self, stream, raw, reason, terminated=True, truncated=False):
        """Retain bounded startup/attachment bytes for the report consumer.

        The canonical-report/integration GoalArtifact consumes this event only
        as diagnostic evidence. It is a distinct kind from signal wire records,
        so it cannot satisfy capability health. Bytes exclude the framing LF;
        terminated records retain that delimiter through the termination flag.
        Truncation is also a retention drop for the existing health consumer.
        """
        if self.sink is None:
            return
        observed_byte_length = len(raw)
        truncated = truncated or observed_byte_length > COLLECTOR_DIAGNOSTIC_LIMIT
        raw = bytes(raw[:COLLECTOR_DIAGNOSTIC_LIMIT])
        if truncated:
            with self.sink.lock:
                self.sink.dropped_events += 1
        self.sink.emit({
            "kind": "collector-diagnostic",
            "stream": stream,
            "reason": reason,
            "terminated": bool(terminated),
            "truncated": bool(truncated),
            "raw_line_sha256": hashlib.sha256(raw).hexdigest(),
            "raw_byte_length": len(raw),
            "observed_byte_length": observed_byte_length,
            "raw_bytes_base64": base64.b64encode(raw).decode("ascii"),
            "encoding": "base64",
            "collector_returncode": self.process.poll() if self.process else None,
        })

    @observed_phase("line-processing")
    def _line(self, line, stream="stdout", raw=None, terminated=True):
        if stream == "stdout" and not line.strip():
            return
        if raw is None:
            raw = line.encode(errors="replace")
        # bpftrace wire is stdout. Stderr is collector-owned diagnostic output,
        # even when its bytes happen to resemble a wire record.
        try:
            if stream != "stdout":
                raise ValueError("collector stderr is not signal wire")
            event = parse_signal_wire(line)
        except (ValueError, OverflowError):
            lost = re.search(r"[Ll]ost\s+(\d+)\s+events", line)
            if lost:
                self.health["lost_events"] += int(lost[1])
                self.sink.emit({"kind": "event-loss", "lost_events": self.health["lost_events"]})
                self._record_collector_diagnostic(stream, raw, reason="collector-event-loss", terminated=terminated)
                return
            self.health["parse_errors"] += 1
            if self.health["parse_errors"] == 1:
                categories = [name for token, name in
                    (("permission", "permission"), ("not permitted", "permission"),
                     ("not found", "missing-probe-or-type"), ("unknown", "missing-probe-or-type"),
                     ("memlock", "memlock"), ("ERROR", "compiler-or-attach")) if token in line]
                self.sink.emit({"kind": "schema-or-capability-error", "categories": sorted(set(categories)),
                                "raw_line_sha256": hashlib.sha256(raw).hexdigest()})
            self._record_collector_diagnostic(
                stream, raw, reason="collector-stderr" if stream != "stdout" else "malformed-output",
                terminated=terminated)
            return
        if self.observation: self.observation.observe_event(event)
        if event["kind"] == "trace-ready":
            self.health["ready"] = True
            self.ready.set()
        if self.fixture and event["kind"] in ("signal", "delivery", "kill", "fork", "exit"):
            if len(self.events) < 10000:
                self.events.append(event)
            else:
                self.health["parse_errors"] += 1
        # Retain every validated kernel record without repeating its expanded
        # clock/identity field names. Fixture memory consumes the parsed event;
        # file/live consumers recover exactly that event through the decoder.
        self.sink.emit(event if event["kind"] == "trace-ready" else
                       {"kind": event["kind"], "wire": line})

    def snapshot(self):
        health = dict(self.health, dropped_events=self.sink.dropped_events if self.sink else 0,
                      retention_error=self.sink.retention_error if self.sink else None,
                      console_error=self.sink.console_error if self.sink else None,
                      collector_returncode=self.process.poll() if self.process else None)
        return health

    def check(self):
        health = self.snapshot()
        if self.process is None or self.process.poll() is not None:
            raise TraceHealthError("collector-not-alive", health)
        try:
            require_trace_health(health)
        except ValueError as error:
            raise TraceHealthError("invalid-trace-health", health) from error

    def stop(self):
        if self.process is not None and self.process.poll() is None:
            # bpftrace's documented orderly detach signal, to this tracer only.
            self.process.send_signal(signal.SIGINT)
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
        if self.thread:
            self.thread.join(timeout=6)
            if self.thread.is_alive():
                self.health["reader_error"] = "reader-did-not-finish"
        if self.sink and not self.sink.closed:
            self.sink.finish(self.snapshot())
        return self.snapshot()


def emit_process_catalog(sink, root_pid):
    rows = {}
    for path in Path("/proc").iterdir():
        if path.name.isdigit():
            try:
                row = proc_row(path)
                rows[row["pid"]] = {k: row.get(k) for k in
                    ("pid", "ppid", "pgid", "sid", "start_ticks", "comm", "exe_basename")}
            except (OSError, ValueError, IndexError):
                pass
    # The bounded trace sink limits even an unexpectedly large host catalog.
    for row in rows.values():
        role = ("Listener" if row["exe_basename"] == "Runner.Listener" else
                "Worker" if row["exe_basename"] == "Runner.Worker" else
                "diagnostic-root" if row["pid"] == root_pid else "host-process")
        sink.emit({"kind": "process-catalog", **stamp(), **row, "role": role,
                   "identity_limit": "proc snapshot; kernel event start identities are authoritative at events"})
    listeners = [row for row in rows.values() if row["exe_basename"] == "Runner.Listener"]
    workers = [row for row in rows.values() if row["exe_basename"] == "Runner.Worker"]
    ancestors = set()
    current = root_pid
    while current in rows and current not in ancestors:
        ancestors.add(current)
        current = rows[current]["ppid"]
    if (len([row for row in workers if row["pid"] in ancestors]) != 1
            or len([row for row in listeners if row["pid"] in ancestors]) != 1):
        raise ValueError("hosted Worker/Listener identities or ancestry unavailable")
    return {"Worker": [row for row in workers if row["pid"] in ancestors],
            "Listener": [row for row in listeners if row["pid"] in ancestors]}


def fixture_identity():
    row = {"pid": os.getpid(), "tgid": os.getpid(), "ppid": os.getppid(),
           "pgid": os.getpgrp(), "sid": os.getsid(0)}
    if sys.platform == "linux":
        row["start_ticks"] = proc_row(Path("/proc") / str(os.getpid()))["start_ticks"]
    return row


def known_sender_fixture(output, sink=None):
    evidence = []
    for mode in ("individual", "group"):
        targets = []
        try:
            leader = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "fixture-target"],
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, process_group=0)
            targets.append(leader)
            if mode == "group":
                targets.append(subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "fixture-target"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, process_group=leader.pid))
            identities = []
            for target in targets:
                readable, _, _ = __import__("select").select([target.stdout], [], [], 5)
                if not readable:
                    raise ValueError("isolated fixture target readiness timeout")
                identity = json.loads(target.stdout.readline())
                if identity["pgid"] != leader.pid or identity["pgid"] == os.getpgrp():
                    raise ValueError("fixture group is not isolated")
                identities.append(identity)
            sender = subprocess.run([sys.executable, str(Path(__file__).resolve()), "fixture-sender",
                                     str(leader.pid), mode], capture_output=True, timeout=5)
            sender_id = json.loads(sender.stdout)
            row = {"kind": "known-sender-fixture", "mode": mode, "signal": int(signal.SIGTERM),
                   "sender": sender_id, "targets": identities, "pgid": leader.pid,
                   "sender_returncode": sender.returncode,
                   "target_returncodes": [target.wait(timeout=5) for target in targets]}
            if sender.returncode or any(rc != -signal.SIGTERM for rc in row["target_returncodes"]):
                raise ValueError("isolated signal fixture failed")
            evidence.append(row)
            append(output / "fixtures.jsonl", row)
            if sink:
                sink.emit(row)
            else:
                print("SIGNAL_DIAGNOSTIC " + json.dumps(row, sort_keys=True), flush=True)
        finally:
            for target in targets:
                if target.poll() is None:
                    target.kill()
                target.wait(timeout=5)
                target.stdout.close()
                target.stderr.close()
    return evidence


def validate_fixture_attribution(events, fixtures):
    events = [decode_signal_record(event) for event in events]
    hz = os.sysconf("SC_CLK_TCK")
    def matches(actual, expected):
        return (actual.get("pid") == expected.get("pid", expected["tgid"])
                and actual.get("tgid") == expected["tgid"] and actual.get("start_ns", 0) > 0
                and ("start_ns" not in expected or actual["start_ns"] == expected["start_ns"])
                and all(actual.get(k) == expected[k] for k in ("ppid", "pgid", "sid") if k in expected)
                and ("start_ticks" not in expected or actual["start_ns"] * hz // 1000000000 == expected["start_ticks"]))
    for fixture in fixtures:
        sender = fixture["sender"]
        signed = -fixture["pgid"] if fixture.get("mode") == "group" else fixture["targets"][0]["pid"]
        if not any(e["kind"] == "kill" and e["signal"] == 15 and e["requested_target"] == signed
                   and matches(e["sender"], sender) for e in events):
            raise ValueError("missing or ambiguous known-sender signed kill event")
        for target in fixture["targets"]:
            if not any(e["kind"] == "signal" and e["signal"] == 15 and matches(e["sender"], sender)
                       and matches(e["target"], target) and e["group"] == 1
                       and e["result"] == 0 for e in events):
                raise ValueError("missing or ambiguous known-sender signal event")
            if not any(e["kind"] == "delivery" and e["signal"] == 15 and matches(e["target"], target)
                       for e in events):
                raise ValueError("fixture signal delivery unavailable")
            if not any(e["kind"] == "exit" and e["kernel_exit_code"] == 15 and matches(e["actor"], target)
                       for e in events):
                raise ValueError("fixture exit identity unavailable")


def capability_preflight(output, trace):
    trace.fixture = True
    fixtures = known_sender_fixture(output, trace.sink)
    # perf event delivery is asynchronous, with a fixed bounded drain window.
    deadline = time.monotonic() + 5
    while True:
        trace.check()
        try:
            validate_fixture_attribution(trace.events, fixtures)
            break
        except ValueError:
            if time.monotonic() >= deadline:
                raise
            threading.Event().wait(.05)
    trace.fixture = False
    trace.events.clear()
    trace.check()
    # Genuine same-kernel ownership/cancellation tests are a capability consumer,
    # not a canonical workload. No compiler, report or interposition is invoked.
    fixture_program = Path(__file__).with_name("tests") / "test_cold_cost.py"
    fixture_rc = observe_command([sys.executable, str(fixture_program), "LinuxOwnershipTests"],
                                 Path(__file__).resolve().parents[3], output,
                                 "ownership-capability-fixtures", dict(os.environ), signal_trace=trace,
                                 deadline_seconds=45)
    if fixture_rc != 0:
        raise ValueError("native operation ownership/cancellation capability failed")
    trace.check()
    result = {"kind": "capability-preflight", "status": "passed", **stamp(),
              "schema": "BTF task identity with exact start time; actual individual/group sender fixtures",
              "ownership": "dedicated Linux operation subreaper; six genuine ownership/cancellation fixtures passed",
              "scope": "this actual kernel/collector interval only; no integration qualification"}
    write_json(output / "preflight.json", result)
    trace.sink.emit(result)
    return result


def compiler(args):
    output = Path(os.environ["COLD_COST_OUTPUT"])
    real = os.environ["COLD_COST_REAL_LEAN"]
    sources = [Path(arg).resolve() for arg in args if arg.endswith(".lean") and Path(arg).is_file()]
    if not sources or "--run" in args:
        os.environ["COLD_COST_INTERNAL"] = "1"
        os.execv(real, [real] + args)
    token = f"{os.getpid()}-{time.monotonic_ns()}"
    folder = output / "compilers" / token
    folder.mkdir(parents=True)
    events = folder / "events.jsonl"
    setup = None
    for i, arg in enumerate(args):
        if arg == "--setup" and i + 1 < len(args):
            setup = Path(args[i + 1])
        elif arg.startswith("--setup="):
            setup = Path(arg.split("=", 1)[1])
    if setup and setup.is_file():
        shutil.copyfile(setup, folder / "setup.json")
    actual = [real, "--profile"] + args
    start = {"kind": "compiler-start", **stamp(), "wrapper_pid": os.getpid(),
             "wrapper_role": "compiler-observer-wrapper", "compiler_role": "real-compiler",
             "terminal_accounting": "pending; absent compiler-end means censored status and resources",
             "argument_count": len(args), "profile_enabled": True,
             "sources": [{"path": str(p), "sha256": sha(p)} for p in sources],
             "profiling": "Lean --profile, default 100ms individual threshold; exclusive component times"}
    child = subprocess.Popen(actual, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             env=dict(os.environ, COLD_COST_INTERNAL="1"))
    start["spawn_return_monotonic_ns"] = time.monotonic_ns()
    received = []

    def forward(sig, _frame):
        received.append(sig)
        try:
            # wait4 is the sole status owner; Popen.send_signal polls/reaps.
            if child.returncode is None:
                os.kill(child.pid, sig)
        except ProcessLookupError:
            pass

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, forward)
    start["compiler_pid"] = child.pid
    if sys.platform == "linux":
        try:
            start["compiler_start_ticks"] = proc_row(Path("/proc") / str(child.pid))["start_ticks"]
        except (OSError, ValueError, IndexError):
            start["compiler_start_ticks"] = None
    append(events, start)
    errors = []

    def relay(pipe, destination, name):
        try:
            with (folder / name).open("wb") as log:
                while True:
                    block = os.read(pipe.fileno(), 65536)
                    if not block:
                        break
                    log.write(block)
                    log.flush()
                    try:
                        destination.write(block)
                        destination.flush()
                    except BrokenPipeError:
                        # Retain evidence even if Lake's output reader was killed.
                        destination = None
                    if destination is None:
                        destination = open(os.devnull, "wb")
        except Exception as error:
            errors.append(type(error).__name__)
        finally:
            pipe.close()

    relays = [threading.Thread(target=relay, args=(child.stdout, sys.stdout.buffer, "stdout.log")),
              threading.Thread(target=relay, args=(child.stderr, sys.stderr.buffer, "stderr.log"))]
    for relay_thread in relays:
        relay_thread.start()
    _, status, usage = os.wait4(child.pid, 0)
    child.returncode = os.waitstatus_to_exitcode(status)
    append(events, {"kind": "compiler-end", **stamp(), "compiler_pid": child.pid,
                    "terminal_accounting": "collected",
                    "wait_status": status, "returncode": child.returncode,
                    "received_signals": received, "rusage_scope": "kernel wait4 child accounting; includes threads and may include waited descendants",
                    "user_cpu_seconds": usage.ru_utime, "system_cpu_seconds": usage.ru_stime,
                    "maxrss": usage.ru_maxrss, "maxrss_unit": "KiB" if sys.platform == "linux" else "bytes",
                    "minor_faults": usage.ru_minflt, "major_faults": usage.ru_majflt,
                    "voluntary_context_switches": usage.ru_nvcsw,
                    "involuntary_context_switches": usage.ru_nivcsw})
    for relay_thread in relays:
        relay_thread.join()
    if errors:
        write_json(folder / "observer-errors.json", errors)
    if child.returncode < 0:
        sig = -child.returncode
        if sig not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(sig, signal.SIG_DFL)
        os.kill(os.getpid(), sig)
    return child.returncode


def build_spawn_observer(output):
    library = output / "cold-cost-spawn.so"
    subprocess.run(["cc", "-shared", "-fPIC", "-Wall", "-Wextra", "-Werror", "-O2",
                    str(Path(__file__).with_name("cold_cost_spawn.c")), "-o", str(library), "-ldl"], check=True)
    return library


def proc_row(path):
    text = (path / "stat").read_text()
    # comm may contain spaces and parentheses; fields after its closing ')'.
    fields = text[text.rfind(")") + 2:].split()
    row = {"pid": int(path.name), "state": fields[0], "ppid": int(fields[1]), "pgid": int(fields[2]), "sid": int(fields[3]),
           "user_ticks": int(fields[11]), "system_ticks": int(fields[12]),
           "start_ticks": int(fields[19]), "rss_pages": int(fields[21])}
    row["comm"] = text[text.find("(") + 1:text.rfind(")")]
    try:
        row["exe_basename"] = Path(os.readlink(path / "exe")).name
    except OSError:
        row["exe_basename"] = None
    row["argv"] = (path / "cmdline").read_bytes().decode(errors="replace").split("\0")[:-1]
    for name in ("status", "io", "schedstat"):
        try:
            row[name] = (path / name).read_text()
        except OSError:
            row[name] = None
    return row


def sample(root_pid, proc=Path("/proc"), cgroup_root=Path("/sys/fs/cgroup"), real_lean=None,
           command_pid=None):
    started_ns = time.monotonic_ns()
    rows = {}
    for path in proc.iterdir():
        if path.name.isdigit():
            try:
                rows[int(path.name)] = proc_row(path)
            except (OSError, ValueError, IndexError):
                pass  # /proc processes can disappear between individual reads.
    members = {root_pid}
    while True:
        more = {pid for pid, row in rows.items() if row["ppid"] in members}
        if more <= members:
            break
        members |= more
    wrapper_argv = [str(Path(__file__).resolve()), "compiler"]
    sampler_pid = os.getpid()
    wrappers = {pid for pid, row in rows.items() if row["argv"][1:3] == wrapper_argv}
    processes = []
    for pid in sorted(members):
        if pid not in rows:
            continue
        row = rows[pid]
        if pid == sampler_pid:
            role = "python-stage-sampler"
        elif pid in wrappers:
            role = "compiler-observer-wrapper"
        elif real_lean and row["argv"][:1] == [real_lean] and row["ppid"] in wrappers:
            role = "real-compiler"
        elif pid == root_pid:
            role = "operation-ownership-supervisor" if command_pid is not None else "command-root"
        elif pid == command_pid:
            role = "command-root"
        elif any(Path(arg).name == "report-supervisor.sh" for arg in row["argv"]):
            role = "report-supervisor"
        elif any(Path(arg).name == "inspect.sh" for arg in row["argv"]):
            role = "inspector-shell"
        elif row.get("exe_basename") == "lean":
            role = "lean-process"
        else:
            role = "unclassified-command-descendant"
        processes.append({**{k: v for k, v in row.items() if k != "argv"}, "role": role})
    kernel = {}
    for name in ("stat", "meminfo", "vmstat", "loadavg", "pressure/cpu", "pressure/memory", "pressure/io"):
        try:
            kernel[name] = (proc / name).read_text()
        except OSError:
            kernel[name] = None
    try:
        entry = next(line[3:] for line in (proc / str(root_pid) / "cgroup").read_text().splitlines()
                     if line.startswith("0::"))
        cgroup = cgroup_root / entry.lstrip("/")
        cg = {"path": str(cgroup)}
        for name in ("cpu.stat", "cpu.max", "cpu.pressure", "memory.current", "memory.peak",
                     "memory.max", "memory.events", "memory.swap.current", "memory.swap.max",
                     "memory.pressure", "io.pressure", "io.stat", "pids.current", "pids.max"):
            try:
                cg[name] = (cgroup / name).read_text()
            except OSError:
                cg[name] = None
    except (OSError, StopIteration):
        cg = None
    return {"kind": "sample", **stamp(),
            "scope": "sampled operation boundary and descendants; includes compiler observer wrappers and canonical shell sampler activity",
            "python_sampler": {"pid": sampler_pid, "role": "python-stage-sampler",
                               "in_processes": sampler_pid in members and sampler_pid in rows},
            "role_basis": "current argv and parent; other descendants, including unidentified shell samplers, remain unclassified",
            "collection_start_monotonic_ns": started_ns, "collection_elapsed_ns": time.monotonic_ns() - started_ns,
            "clock_ticks_per_second": os.sysconf("SC_CLK_TCK"), "page_bytes": os.sysconf("SC_PAGE_SIZE"),
            "processes": processes,
            "kernel_scope": "host cumulative counters/pressure, including observer activity", "kernel": kernel,
            "cgroup_scope": "command cgroup (may include Python observer and other job processes)", "cgroup": cg}


def enable_subreaper():
    # Linux PR_SET_CHILD_SUBREAPER / PR_GET_CHILD_SUBREAPER. The attribute is
    # installed in a dedicated process before its only workload is spawned.
    # https://man7.org/linux/man-pages/man2/PR_SET_CHILD_SUBREAPER.2const.html
    if sys.platform != "linux":
        raise ValueError("Linux operation subreaper unavailable; workload forbidden")
    libc = ctypes.CDLL(None, use_errno=True)
    libc.prctl.argtypes = [ctypes.c_int] + [ctypes.c_ulong] * 4
    libc.prctl.restype = ctypes.c_int
    value = ctypes.c_int()
    if (libc.prctl(36, 1, 0, 0, 0) != 0
            or libc.prctl(37, ctypes.addressof(value), 0, 0, 0) != 0 or value.value != 1):
        raise OSError(ctypes.get_errno(), "operation subreaper unavailable")


def owned_rows(supervisor_pid):
    """Current subtree of the stable subreaper, independent of sampled ancestry.

    Orphans remain under this boundary even after root exit, setsid or setpgid.
    Only stat identity is needed; optional observer fields have no authority.
    Numeric identity-check/signal races remain a limitation.
    """
    rows = {}
    pending = [supervisor_pid]
    visited = set()
    while pending:
        pid = pending.pop()
        if pid in visited:
            continue
        visited.add(pid)
        try:
            tasks = list((Path("/proc") / str(pid) / "task").iterdir())
        except (FileNotFoundError, ProcessLookupError):
            continue
        for task in tasks:
            try:
                children = (task / "children").read_text().split()
            except (FileNotFoundError, ProcessLookupError):
                continue
            for child in map(int, children):
                try:
                    text = (Path("/proc") / str(child) / "stat").read_text()
                except (FileNotFoundError, ProcessLookupError):
                    continue
                fields = text[text.rfind(")") + 2:].split()
                rows[child] = {"pid": child, "start_ticks": int(fields[19])}
                pending.append(child)
    return [rows[pid] for pid in sorted(rows)]


def owned_supervisor(fd, command):
    """The only child-owning process for one finite passive operation.

    This process creates no tracer or unrelated children. It stays alive until
    waitpid reports ECHILD, which verifies the whole adopted workload is reaped.
    Unkillable tasks, malicious workloads and supervisor destruction are outside
    the supported cleanup guarantee; incomplete cleanup is never success.
    """
    channel = socket.socket(fileno=fd)
    root = None
    root_rc = None
    stopping = None
    targeted = set()
    term_sent = set()
    error = None
    def send(value):
        channel.sendall((json.dumps(value) + "\n").encode())
    try:
        enable_subreaper()
        # The observer signals via the private channel, never this supervisor's
        # group. The command retains its own original private process group.
        root = subprocess.Popen(command, process_group=0)
        send({"kind": "root-start", "pid": root.pid})
        while True:
            no_children = False
            while True:
                try:
                    pid, status = os.waitpid(-1, os.WNOHANG)
                except ChildProcessError:
                    no_children = True
                    break
                if pid == 0:
                    break
                if pid == root.pid:
                    root_rc = os.waitstatus_to_exitcode(status)
                    root.returncode = root_rc
                    send({"kind": "root-exit", "returncode": root_rc})
                    if stopping is None:
                        stopping = time.monotonic()
            if no_children:
                send({"kind": "complete", "returncode": root_rc,
                      "cleanup": {"command_pgid": root.pid, "root_reaped": root_rc is not None,
                                  "workload_reaped": True, "supervisor_pid": os.getpid(),
                                  "identity_checked_descendants": sorted(targeted)}})
                return 0
            readable, _, _ = __import__("select").select([channel], [], [], .02)
            if readable:
                message = channel.recv(4096)
                if (not message or b"stop" in message) and stopping is None:
                    stopping = time.monotonic()
            if stopping is not None:
                elapsed = time.monotonic() - stopping
                sig = signal.SIGTERM if elapsed < 2 else signal.SIGKILL
                for row in owned_rows(os.getpid()):
                    identity = (row["pid"], row["start_ticks"])
                    if sig == signal.SIGTERM and identity in term_sent:
                        continue
                    # Recheck the minimal start identity before numeric signaling.
                    try:
                        text = (Path("/proc") / str(row["pid"]) / "stat").read_text()
                        if int(text[text.rfind(")") + 2:].split()[19]) != row["start_ticks"]:
                            continue
                        os.kill(row["pid"], sig)
                        targeted.add(row["pid"])
                        term_sent.add(identity)
                    except (FileNotFoundError, ProcessLookupError):
                        pass
                if elapsed >= 4:
                    raise TimeoutError("owned workload did not become fully waitable")
    except BaseException as caught:
        error = type(caught).__name__
        # Capability errors precede spawn. Runtime failure is explicitly censored.
        try:
            send({"kind": "supervisor-error", "error": error, "returncode": root_rc,
                  "cleanup": {"root_reaped": root_rc is not None, "workload_reaped": False}})
        except OSError:
            pass
        return 2
    finally:
        channel.close()


class OwnedCommand:
    def __init__(self, command, **kwargs):
        self.channel, peer = socket.socketpair()
        self.process = None
        self.pid = None
        self.returncode = None
        self.cleanup = None
        self.error = None
        self.buffer = b""
        try:
            self.process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()),
                "owned-supervisor", str(peer.fileno()), *command], pass_fds=(peer.fileno(),),
                process_group=0, **kwargs)
        except BaseException:
            self.channel.close()
            raise
        finally:
            peer.close()
        self.channel.setblocking(False)

    def poll(self):
        supervisor_rc = self.process.poll()
        while True:
            try:
                block = self.channel.recv(65536)
            except BlockingIOError:
                break
            if not block:
                break
            self.buffer += block
            while b"\n" in self.buffer:
                line, self.buffer = self.buffer.split(b"\n", 1)
                row = json.loads(line)
                if row["kind"] == "root-start":
                    self.pid = row["pid"]
                elif row["kind"] == "root-exit":
                    self.returncode = row["returncode"]
                elif row["kind"] in ("complete", "supervisor-error"):
                    self.returncode = row.get("returncode")
                    self.cleanup = row["cleanup"]
                    self.error = row.get("error")
        if supervisor_rc is not None:
            if self.cleanup is None or not self.cleanup.get("workload_reaped") or self.error:
                raise ValueError("owned workload cleanup unavailable: " + str(self.error))
            return self.returncode
        return None

    def stop(self):
        try:
            self.channel.sendall(b"stop\n")
        except (BrokenPipeError, ConnectionResetError):
            pass
        deadline = time.monotonic() + 5
        while self.process.poll() is None and time.monotonic() < deadline:
            self.poll()
            threading.Event().wait(.02)
        self.process.wait(timeout=.5)
        self.poll()
        return self.cleanup

    def close(self):
        self.channel.close()


def stop_owned_command(child, processes=()):
    # Ownership comes from the operation subreaper, never observer snapshots.
    return child.stop()


@cancellable
def observe_command(command, cwd, output, name, env, interval=2.0, canonical_resources=False,
                    signal_sink=None, signal_trace=None, deadline_seconds=None):
    if signal_trace is not None:
        signal_trace.check()
        signal_sink = signal_trace.sink
    events = output / "stages.jsonl"
    begin = stamp()
    deadline = None if deadline_seconds is None else time.monotonic() + deadline_seconds
    with (output / f"{name}.stdout.log").open("wb") as stdout, (output / f"{name}.stderr.log").open("wb") as stderr:
        actual = command
        if canonical_resources:
            actual = ["bash", "-c", 'source tools/scripts/lib/resource-observation-lib.sh; resource_observe_run_periodic "$@"',
                      "cold-cost"] + command
        child = None
        failure = None
        cleanup = None
        try:
            check_cancellation()
            child = OwnedCommand(actual, cwd=cwd, env=env, stdout=stdout, stderr=stderr)
            # Signal handlers latch across constructor/Popen, including a signal
            # after successful spawn but before this assignment and try body.
            check_cancellation()
            startup_deadline = time.monotonic() + 5
            while child.pid is None:
                check_cancellation()
                child.poll()
                if time.monotonic() >= startup_deadline:
                    raise TimeoutError("operation supervisor startup")
                threading.Event().wait(.01)
            stage_event = {"kind": "stage-start", "name": name, "program_basename": Path(command[0]).name,
                           "canonical_resources": canonical_resources, "pid": child.pid,
                           "ownership_supervisor_pid": child.process.pid, **begin}
            append(events, stage_event)
            if signal_sink:
                signal_sink.emit(stage_event)
            next_sample = time.monotonic()
            while True:
                check_cancellation()
                if deadline is not None and time.monotonic() >= deadline:
                    raise TimeoutError("diagnostic capability fixture deadline")
                if signal_trace is not None:
                    signal_trace.check()
                if child.poll() is not None:
                    break
                if time.monotonic() >= next_sample:
                    try:
                        observation = vars(signal_trace).get("observation") if signal_trace is not None else None
                        with observation_span(observation, "sample-collection"):
                            sample_event = {"stage": name, **sample(child.process.pid, real_lean=env.get("COLD_COST_REAL_LEAN"),
                                                                  command_pid=child.pid)}
                        if observation:
                            if "collection_elapsed_ns" in sample_event:
                                observation.add("sample_collection_elapsed_ns", sample_event["collection_elapsed_ns"])
                            else: observation.add("sample_collection_span_unavailable")
                        with observation_span(observation, "sample-append"):
                            append(output / "samples.jsonl", sample_event)
                        with observation_span(observation, "sample-emission"):
                          if signal_sink:
                            for row in sample_event["processes"]:
                                signal_sink.emit({"kind": "stage-process", "stage": name, **stamp(),
                                    **{k: row.get(k) for k in ("pid", "ppid", "pgid", "sid", "start_ticks", "comm", "exe_basename", "role")}})
                    except Exception as error:
                        append(output / "observer-errors.jsonl", {"stage": name, **stamp(), "error": type(error).__name__})
                        raise
                    next_sample = time.monotonic() + interval
                if signal_trace is not None:
                    signal_trace.check()
                threading.Event().wait(min(.1, max(.001, next_sample - time.monotonic())))
            check_cancellation()
            if signal_trace is not None:
                signal_trace.check()
            cleanup = child.cleanup
        except BaseException as error:
            failure = {"error": type(error).__name__, "retention": "censored",
                       "signal": error.signum if isinstance(error, CommandCancelled) else None,
                       "reason": error.reason if isinstance(error, TraceHealthError) else None,
                       "trace_health": signal_trace.snapshot() if signal_trace is not None else None}
            if child is not None:
                try:
                    cleanup = stop_owned_command(child)
                except BaseException as cleanup_error:
                    cleanup = {**(child.cleanup or {}), "workload_reaped": False,
                               "error": type(cleanup_error).__name__}
                error.command_returncode = child.returncode
            raise
        finally:
            try:
                append(events, {"kind": "stage-end", "name": name, **stamp(),
                                "returncode": child.returncode if child else None,
                                "observer_failure": failure, "cleanup": cleanup})
            finally:
                if child is not None:
                    child.close()
    return child.returncode


def observe_output(command, cwd, output, name, env, trace):
    rc = observe_command(command, cwd, output, name, env, signal_trace=trace)
    stdout = (output / f"{name}.stdout.log").read_bytes()
    if rc:
        raise subprocess.CalledProcessError(rc, command, output=stdout)
    return stdout


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def input_binding(root):
    paths = ["D5", "Reg", "Blueprint", "Golden/Frozen", "Trureturing.lean", "lean-toolchain", "lakefile.toml",
             "lake-manifest.json", "lean-report-inputs.json", "tools/lean-inspector",
             "tools/lean-inspector-interface", "tools/lean-inspector-reg", "tools/scripts/report/report-supervisor.sh",
             "tools/scripts/compiled-judge-test.sh", "tools/scripts/worktree/lean-cache-run.sh"]
    listing = git(root, "ls-tree", "-r", "-z", "HEAD", "--", *paths)
    files = [row.split("\t", 1)[1] for row in listing.decode().split("\0") if row]
    return {"paths": paths, "git_blob_listing_sha256": hashlib.sha256(listing).hexdigest(),
            "listing": listing.decode().split("\0")[:-1],
            "actual_file_sha256": {name: sha(root / name) for name in files}}


PRODUCTION_H = "fd3aedf362d79cdc0bc91219ef8b7ff876e36cd8"
PRODUCTION_M = "d3c904ef7ab2a9bb3d4ac1ec7bcf9bcc661b3290"
PRODUCTION_B = "05c38482fd9aaf69e4ec78a9fc9828143084d898"
PRODUCTION_TREE = "014fe3f02f608c77d9ccafef105ae8f38c88c981"
PRODUCTION_LISTING_SHA256 = "ae7636645f307ed30e5a47fd104d3229f2932475c10b02c64dc6855c1f806013"
PRODUCTION_FILEMAP_SHA256 = "007bb81d1496e5c33fd34af5b5adcffe7e2776972ae0ea51f20e34c762c38d3d"
DIAGNOSTIC_PATHS = ('.github/workflows/lean-cold-cost.yml', 'Meta/FILEMAP.toml', 'tools/scripts/report/cold_cost.py', 'tools/scripts/report/cold_cost_spawn.c', 'tools/scripts/report/tests/test_cold_cost.py')


OBSERVATION_BASE = "ed9b30f560520f7a785dc44b2cd5e0883bdea4f5"
OBSERVATION_PATHS = frozenset((
    ".github/workflows/lean-cold-cost.yml",
    "tools/scripts/report/cold_cost.py", "tools/scripts/report/report-supervisor.sh",
    "tools/scripts/lib/resource-observation-lib.sh", "tools/scripts/report/tests/test_cold_cost.py",
    "tools/tests/StrataLint.ReportSupervisor.Tests/ReportSupervisorScriptTests.cs",
    "tools/tests/StrataLint.ResourceObservation.Tests/ResourceObservationLibraryTests.cs"))


def observation_binding(root, value, source_head, merge_head):
    """Consume an exact root-reviewed observation manifest in the PR body.

    This provenance exception substitutes original blobs only to verify the
    unchanged production/input seals. Observation hashes are never cache/report
    reuse inputs. Event/source approval is owned outside this diagnostic worker.
    """
    if (not isinstance(value, dict) or set(value) != {"schema", "diagnostic_base", "source_H", "source_tree", "merge_M", "B", "production", "delta"}
            or value["schema"] != 1 or value["diagnostic_base"] != OBSERVATION_BASE
            or value["source_H"] != source_head or value["merge_M"] != merge_head
            or value["B"] != PRODUCTION_B
            or value["production"] != {"H": PRODUCTION_H, "M": PRODUCTION_M, "tree": PRODUCTION_TREE}
            or value["source_tree"] != git(root, "rev-parse", source_head + "^{tree}").decode().strip()):
        raise ValueError("observation source/production identity differs from reviewed binding")
    delta = value["delta"]
    changed = set(git(root, "diff", "--name-only", OBSERVATION_BASE, source_head, "--").decode().splitlines())
    if not isinstance(delta, dict) or not delta or set(delta) != changed or not changed <= OBSERVATION_PATHS:
        raise ValueError("observation delta differs from exact reviewed owner set")
    for name, item in delta.items():
        if (not isinstance(item, dict) or set(item) != {"before_blob", "after_blob", "sha256"}
                or item["before_blob"] != git(root, "rev-parse", OBSERVATION_BASE + ":" + name).decode().strip()
                or item["after_blob"] != git(root, "rev-parse", source_head + ":" + name).decode().strip()
                or item["after_blob"] != git(root, "rev-parse", "HEAD:" + name).decode().strip()
                or item["sha256"] != sha(root / name)):
            raise ValueError("observation owner differs from exact reviewed bytes: " + name)
    return value


def sealed_listing(root, listing, observation):
    if observation is None: return listing
    original = git(root, "ls-tree", "-r", "-z", OBSERVATION_BASE, "--", *observation["delta"])
    rows = {row.split(b"\t", 1)[1].decode(): row for row in original.split(b"\0") if row}
    replaced = []
    for row in listing.split(b"\0"):
        if row:
            name = row.split(b"\t", 1)[1].decode()
            replaced.append(rows[name] if name in observation["delta"] else row)
    return b"\0".join(replaced) + b"\0"


def production_binding(root, observation=None):
    listing = sealed_listing(root, git(root, "ls-tree", "-r", "-z", "HEAD"), observation)
    rows = [row for row in listing.split(b"\0") if row and row.split(b"\t", 1)[1].decode() not in DIAGNOSTIC_PATHS]
    digest = hashlib.sha256(b"\0".join(rows) + b"\0").hexdigest()
    text = (root / "Meta/FILEMAP.toml").read_text()
    expected_entries = []
    for name in DIAGNOSTIC_PATHS:
        if name in ("Meta/FILEMAP.toml", "tools/scripts/report/cold_cost_spawn.c"):
            continue
        expected_entries.append('  { pattern = "' + name + '", kind = "program", admission_plane = "judge", produced_by = "none", consumed_by = ["GitHub-Actions"], verified_by = ["make-gate"], artifact_id = "none", runtime_disposition = "committed-source" },\n')
    for entry in expected_entries:
        if text.count(entry) != 1:
            raise ValueError("diagnostic FILEMAP entries differ from their registered declarations")
        text = text.replace(entry, "")
    if (digest != PRODUCTION_LISTING_SHA256 or hashlib.sha256(text.encode()).hexdigest() != PRODUCTION_FILEMAP_SHA256):
        raise ValueError("non-diagnostic source differs from immutable H/M workload")
    return {"H": PRODUCTION_H, "M": PRODUCTION_M, "B": PRODUCTION_B,
            "production_tree": PRODUCTION_TREE, "nondiagnostic_listing_sha256": digest,
            "filemap_production_sha256": PRODUCTION_FILEMAP_SHA256}


def native_binding(root, env, mode="workload"):

    event = json.loads(Path(env["GITHUB_EVENT_PATH"]).read_text())
    head = git(root, "rev-parse", "HEAD").decode().strip()
    parents = git(root, "show", "-s", "--format=%P", "HEAD").decode().split()
    if (env.get("GITHUB_ACTIONS") != "true" or env.get("GITHUB_EVENT_NAME") != "pull_request"
            or event.get("action") != "labeled" or head != env.get("GITHUB_SHA")
            or event.get("label", {}).get("name") != ("cold-cap-" if mode == "preflight" else "cold-cost-") + head
            or len(parents) != 2 or parents[1] != event["pull_request"]["head"]["sha"]):
        raise ValueError("requires genuine labeled PR merge candidate matching the reviewed merge SHA")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("source checkout must be clean")
    observation = None
    body = event["pull_request"].get("body") or ""
    matches = re.findall(r"```cold-cost-observation\n(.*?)\n```", body, re.DOTALL)
    if matches:
        if len(matches) != 1 or parents[0] != PRODUCTION_B:
            raise ValueError("ambiguous observation binding or changed protected base")
        observation = observation_binding(root, json.loads(matches[0], object_pairs_hook=_unique_json_object), parents[1], head)
    production = production_binding(root, observation) if observation is not None else production_binding(root)
    inputs = input_binding(root)
    input_listing = git(root, "ls-tree", "-r", "-z", "HEAD", "--", *inputs["paths"]) if observation is not None else None
    sealed_inputs = (hashlib.sha256(sealed_listing(root, input_listing, observation)).hexdigest()
                     if observation is not None else inputs["git_blob_listing_sha256"])
    if sealed_inputs != SEALED_INPUTS_SHA256:
        raise ValueError("registered source/compiler/report inputs differ from the sealed candidate")
    os_release = Path("/etc/os-release").read_text()
    if platform.system() != "Linux" or platform.machine() != "aarch64" or 'VERSION_ID="24.04"' not in os_release or 'ID=ubuntu' not in os_release:
        raise ValueError("requires ubuntu-24.04-arm")
    if (root / ".lake").exists():
        raise ValueError("project must start cold: .lake must be absent, no project seed restore")
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
        raise ValueError("requires official Lean v4.34.1")
    for path in (root / "lake-manifest.json", root / "Reg/lake-manifest.json",
                 root / "tools/lean-inspector/lake-manifest.json", root / "tools/lean-inspector-interface/lake-manifest.json",
                 root / "tools/lean-inspector-reg/lake-manifest.json"):
        packages = json.loads(path.read_text())["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        if mathlib["rev"] != "d13f23b723b8a846827a245b89c10fc7d3f11612":
            raise ValueError(f"wrong mathlib pin: {path}")
    forbidden = [key for key in env if key.startswith("STRATALINT_") and key not in
                 {"STRATALINT_ACCEPT_COLD_BUILD", "STRATALINT_CACHE_WRITES"}]
    if forbidden or any(key in env for key in ("LEAN_SYSROOT", "LEAN", "LAKE_OVERRIDE_LEAN", "LEAN_REPORT", "LEAN_SKIP_LOCK", "LD_PRELOAD", "PREFLIGHT_DEADLINE_AT")):
        raise ValueError(f"unexpected control environment: {forbidden}")
    return {**stamp(), "head": head, "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
            "protected_base": parents[0], "pr_head": parents[1], "production": production, "mode": mode,
            "run_id": int(env.get("GITHUB_RUN_ID", "0")), "run_attempt": int(env.get("GITHUB_RUN_ATTEMPT", "0")),
            "runner": {"os_release": os_release, "machine": platform.machine(), "uname": list(platform.uname())},
            "inputs": inputs, "observation_binding": observation, "sealed_inputs_sha256": sealed_inputs, "project_initial_state": "absent .lake", "report_guard_seconds": 7200}


@cancellable
def run(root, output, mode="workload"):
    if sys.version_info[:2] != (3, 12):
        raise ValueError("requires Python 3.12")
    env = dict(os.environ)
    binding = native_binding(root, env, mode)
    output.mkdir(parents=True, exist_ok=False)
    rc = None
    stage = "observer-setup"
    stages = []
    complete = False
    inputs_unchanged = None
    canonical_failure = None
    observer_failure = None
    trace = None
    preflight = None
    trace_health = None
    observation = LinuxObservation(output)
    observation_result = None
    env["COLD_COST_OBSERVATION_DIR"] = str(output.resolve())

    def result():
        return {**stamp(), "canonical_returncode": rc if observer_failure is None else None,
                "canonical_chain_complete": complete and observer_failure is None, "canonical_stages": stages,
                "canonical_failure": canonical_failure, "observer_failure": observer_failure,
                "diagnostic_only": True, "native_acceptance_or_integration_units": False,
                "inputs_unchanged": inputs_unchanged, "mode": mode,
                "preflight": preflight, "trace_health": trace_health, "observation": observation_result}

    try:
        write_json(output / "source.json", binding)
        check_cancellation()
        observation.start()
        starting_trace = SignalTrace(output, PREFLIGHT_SECONDS if mode == "preflight" else TRACE_SECONDS)
        starting_trace.observation = observation
        trace = starting_trace.start()
        check_cancellation()
        emit_process_catalog(trace.sink, os.getpid())
        preflight = capability_preflight(output, trace)
        check_cancellation()
        if mode == "preflight":
            rc = 0
            return 0
        trace.check()
        real = Path(observe_output(["elan", "which", "lean"], root, output,
                                  "compiler-selection", env, trace).decode().strip()).resolve()
        version = observe_output([str(real), "--version"], root, output,
                                 "compiler-version", env, trace).decode().strip()
        if "version 4.34.1" not in version:
            raise ValueError(f"wrong actual compiler: {version}")
        write_json(output / "compiler.json", {"real_binary": str(real), "sha256": sha(real), "version": version,
                   "githash": observe_output([str(real), "--githash"], root, output,
                                             "compiler-githash", env, trace).decode().strip(),
                   "observation_delta": ["passive kernel trace and existing sampling; invalid trace stops owned diagnostic commands; no compiler profiling changes"],
                   "admission": "canonical checks and budgets unchanged; trace health gates diagnostic execution only"})
        env.update(STRATALINT_ACCEPT_COLD_BUILD="1", STRATALINT_CACHE_WRITES="false")
        env["STRATALINT_LEAN_REPORT_LOG_DIR"] = str(output / "report-phases")
        # Same producer/compiled-judge/full-report chain as the current native job.
        stage = "judge-build"
        rc = observe_command(["make", "-C", "tools", "dotnet", "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"], root, output, stage, env, canonical_resources=True, signal_trace=trace)
        stages.append({"stage": stage, "returncode": rc})
        if rc == 0:
            stage, rc = "judge-lean-producer", None
            try:
                producer = observe_output(["bash", "tools/scripts/workflow/judge-lean-producer.sh",
                            str(root / "tools/StrataLint.Cli/bin/Release/net10.0")], root, output,
                            stage, env, trace).decode().strip()
            except subprocess.CalledProcessError as error:
                rc = error.returncode
                stages.append({"stage": stage, "returncode": rc})
                canonical_failure = {"stage": stage, "returncode": rc, "error": type(error).__name__}
                raise
            stages.append({"stage": stage, "returncode": 0})
            if producer:
                env["STRATALINT_LEAN_PRODUCER_DLL"] = producer
            else:
                env.pop("STRATALINT_LEAN_PRODUCER_DLL", None)
            stage, rc = "compiled-judge-test", None
            rc = observe_command(["make", "compiled-judge-test"], root, output, stage, env, canonical_resources=True, signal_trace=trace)
            stages.append({"stage": stage, "returncode": rc})
        if rc == 0:
            trace.check()
            stage, rc = "full-lean-report", None
            rc = observe_command(["make", "lean-report", "LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build"], root, output, stage, env, canonical_resources=True, signal_trace=trace)
            stages.append({"stage": stage, "returncode": rc})
            trace.check()
            complete = True
        if rc != 0:
            canonical_failure = {"stage": stage, "returncode": rc}
    except BaseException as error:
        if hasattr(error, "command_returncode") and stage in (
                "judge-build", "judge-lean-producer", "compiled-judge-test", "full-lean-report"):
            stages.append({"stage": stage, "returncode": error.command_returncode})
        if canonical_failure is None:
            rc = None
            observer_failure = {"stage": stage, "error": type(error).__name__, "retention": "censored"}
            if isinstance(error, CommandCancelled):
                observer_failure["signal"] = error.signum
            if isinstance(error, TraceHealthError):
                observer_failure.update(reason=error.reason, trace_health=error.health, retention="censored")
        raise
    finally:
        collection_error = None
        def collection_failed(error):
            nonlocal observer_failure, collection_error
            collection_error = error
            observer_failure = {"stage": "artifact-collection", "error": type(error).__name__,
                                "retention": "censored", "prior_observer_failure": observer_failure}
            if _cancellation is not None and _cancellation["signal"] is not None:
                observer_failure["signal"] = _cancellation["signal"]
        def publish_result():
            write_json(output / "result.json", result())
            inventory = [{"path": str(p.relative_to(output)), "sha256": sha(p), "bytes": p.stat().st_size}
                         for p in sorted(output.rglob("*")) if p.is_file()]
            write_json(output / "inventory.json", inventory)
        def terminal_cancel(error):
            # cancellation_scope owns normal-return handoff, including the tail
            # after this finally block. Keep raw stage outcomes, censor success,
            # and bind the corrected result in a fresh inventory when writable.
            collection_failed(error)
            try:
                (output / "inventory.json").unlink(missing_ok=True)
                publish_result()
            except OSError:
                try:
                    (output / "result.json").unlink(missing_ok=True)
                except OSError:
                    pass
        stage = "artifact-collection"
        try:
            if trace is not None:
                trace_health = trace.stop()
        except BaseException as error:
            collection_failed(error)
            trace_health = trace.snapshot()
        observation_result = observation.stop()
        try:
            # Preserve genuine producer origins and receipts; copy bytes, never synthesize.
            report = ".lake/build/stratalint/raw-lean-report.json"
            for relative in tuple(report + suffix for suffix in ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".reuse.json")) + (
                             ".lake/build/lean-inspector/inputs.json", "build/lean-cache/build-work.json"):
                path = root / relative
                if path.is_file():
                    target = output / "canonical" / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)
            inputs_unchanged = input_binding(root) == binding["inputs"]
            if not inputs_unchanged:
                raise ValueError("canonical invocation changed preserved source inputs")
        except BaseException as error:
            collection_failed(error)
        try:
            observer_logs = [p for p in [output / "observer-errors.jsonl", *output.glob("compilers/*/observer-errors.json")]
                             if p.is_file()]
            if observer_logs:
                raise ValueError("observer errors recorded: " + ", ".join(str(p.relative_to(output)) for p in observer_logs))
            if trace_health is not None:
                require_trace_health(trace_health)
        except BaseException as error:
            collection_failed(error)
        try:
            check_cancellation()
            publish_result()
            check_cancellation()
            _cancellation["terminal_cancel"] = terminal_cancel
        except BaseException as error:
            collection_failed(error)
            # An earlier successful result is no longer admissible. Correction
            # is best effort if the result sink itself has become unwritable.
            try:
                write_json(output / "result.json", result())
            except OSError:
                try:
                    (output / "result.json").unlink(missing_ok=True)
                except OSError:
                    pass
        if collection_error is not None:
            raise collection_error
    return rc if rc >= 0 else 128 - rc


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "owned-supervisor":
        return owned_supervisor(int(sys.argv[2]), sys.argv[3:])
    if len(sys.argv) > 1 and sys.argv[1] == "fixture-target":
        # A caught first SIGTERM is delivered as SIGTERM. The kernel's default
        # fatal group-exit path can instead report an internal SIGKILL delivery.
        # Restore default disposition only after receiving the sender's signal,
        # preserving the real SIGTERM termination status for the exit consumer.
        def terminate(signum, _frame):
            print(json.dumps({"kind": "fixture-received-signal", "signal": signum}), flush=True)
            signal.signal(signum, signal.SIG_DFL)
            os.kill(os.getpid(), signum)
        signal.signal(signal.SIGTERM, terminate)
        print(json.dumps(fixture_identity()), flush=True)
        time.sleep(30)
        return 0
    if len(sys.argv) > 1 and sys.argv[1] == "fixture-sender":
        target, mode = int(sys.argv[2]), sys.argv[3]
        if target <= 1 or target == os.getpgrp() or mode not in ("individual", "group"):
            raise ValueError("unsafe fixture target")
        print(json.dumps(fixture_identity()), flush=True)
        (os.killpg if mode == "group" else os.kill)(target, signal.SIGTERM)
        return 0
    if len(sys.argv) > 1 and sys.argv[1] == "compiler":
        return compiler(sys.argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("preflight", "workload"), required=True)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    return run(args.repository.resolve(), args.output.resolve(), args.mode)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except CommandCancelled as error:
        sys.exit(128 + error.signum)
    except (ValueError, KeyError) as error:
        print(f"COLD_COST_ERROR {type(error).__name__}", file=sys.stderr)
        sys.exit(2)
