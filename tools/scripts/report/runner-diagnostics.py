#!/usr/bin/env python3
"""Opt-in Linux runner signal/memory observation; never interpret it as a verdict."""
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time

PREFIX = "RUNNER_DIAGNOSTICS "
SIGNALS = "HUP,INT,TERM,QUIT,ABRT,KILL,USR1,USR2"
OUTPUT_LOCK = threading.Lock()


def emit(kind, **fields):
    try:
        payload = (PREFIX + json.dumps(dict(kind=kind, time_ns=time.time_ns(), **fields),
                                      sort_keys=True) + "\n").encode()
        with OUTPUT_LOCK:
            fd = sys.stdout.fileno()
            # Keep ordinary pipe records atomic relative to business output.
            if len(payload) > os.fpathconf(fd, "PC_PIPE_BUF"):
                payload = (PREFIX + '{"kind":"unavailable","reason":"console-record-too-large"}\n').encode()
            while payload:
                try:
                    written = os.write(fd, payload)
                except InterruptedError:
                    continue
                if written <= 0:
                    break
                payload = payload[written:]
    except (OSError, ValueError):
        pass  # No buffered stdout can change the business exit during shutdown.


def identity(pid):
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
        name, tail = raw[raw.index("(") + 1:].rsplit(")", 1)
        fields = tail.split()
        return dict(pid=int(pid), name=name, ppid=int(fields[1]), pgid=int(fields[2]),
                    sid=int(fields[3]), starttime=int(fields[19]))
    except (OSError, ValueError, IndexError):
        return None


def same_process(record):
    current = identity(record["pid"]) if record is not None else None
    return current is not None and current["starttime"] == record["starttime"]


def worker_ancestor():
    pid, seen = os.getppid(), set()
    while pid > 1 and pid not in seen:
        seen.add(pid)
        record = identity(pid)
        if record is None:
            break
        if record["name"] == "Runner.Worker":
            return record
        pid = record["ppid"]
    return None


def cgroup_directory(pid):
    try:
        relative = next(line[3:] for line in Path(f"/proc/{pid}/cgroup").read_text().splitlines()
                        if line.startswith("0::"))
        for line in Path("/proc/self/mountinfo").read_text().splitlines():
            left, right = line.split(" - ", 1)
            if right.split()[0] == "cgroup2":
                fields = left.split()
                root, mount = Path(fields[3]), Path(fields[4])
                # Reject namespace paths outside the mounted hierarchy.
                suffix = Path(relative).relative_to(root)
                if ".." not in suffix.parts:
                    return mount / suffix
    except (OSError, ValueError, StopIteration, IndexError):
        pass
    return None


def memory_sample(directory):
    result = {}
    if directory is not None:
        for name in ("memory.current", "memory.max", "memory.swap.current", "memory.swap.max"):
            try:
                value = (directory / name).read_text().strip()
                if value == "max" or value.isdigit():
                    result[name] = value if value == "max" else int(value)
            except OSError:
                pass
        try:
            result["memory.events"] = {key: int(value) for key, value in
                (line.split() for line in (directory / "memory.events").read_text().splitlines())}
        except (OSError, ValueError):
            pass
        try:
            result["memory.pressure"] = {}
            for line in (directory / "memory.pressure").read_text().splitlines():
                scope, *metrics = line.split()
                if scope in ("some", "full"):
                    result["memory.pressure"][scope] = {
                        key: float(value) if "." in value else int(value)
                        for key, value in (metric.split("=", 1) for metric in metrics)}
        except (OSError, ValueError):
            pass
    try:
        for key, value in re.findall(r"^(MemTotal|MemAvailable):\s+(\d+) kB$",
                                     Path("/proc/meminfo").read_text(), re.M):
            result[key + "_kb"] = int(value)
    except OSError:
        pass
    return result


def own_group(process, record, number):
    # Both children are created with start_new_session=True. Never infer a group
    # from an unrelated or already-exited leader, nor signal the Worker ancestor.
    current = identity(process.pid)
    if (process.poll() is None and same_process(record) and current is not None
            and current["pid"] == current["pgid"] == current["sid"] == record["pgid"] == record["sid"]):
        try:
            os.killpg(current["pgid"], number)
        except (ProcessLookupError, PermissionError):
            pass


def stop_privileged_tracer(pid, starttime, number):
    """Root helper: signal only an exact owned strace, let sudo reap its child."""
    parent = identity(pid)
    if (parent is None or parent["starttime"] != starttime
            or parent["name"] not in ("sudo", "strace")
            or parent["pid"] != parent["pgid"] or parent["pid"] != parent["sid"]
            or number not in (signal.SIGTERM, signal.SIGKILL)):
        return []
    candidates, pending, seen = [], [parent], set()
    while pending:
        record = pending.pop()
        if record["pid"] in seen or not same_process(record):
            continue
        seen.add(record["pid"])
        if record["name"] == "strace":
            candidates.append(record)
        try:
            children = Path(f"/proc/{record['pid']}/task/{record['pid']}/children").read_text().split()
            for child in children:
                child_record = identity(int(child))
                if child_record is not None and child_record["ppid"] == record["pid"]:
                    pending.append(child_record)
        except OSError:
            pass
    stopped = []
    for record in candidates:
        if same_process(record):
            try:
                os.kill(record["pid"], number)
                stopped.append(record["pid"])
            except ProcessLookupError:
                pass
    return stopped


class Observer:
    def __init__(self):
        self.stop = threading.Event()
        self.attached = threading.Event()
        self.sampler = self.reader = self.tracer = self.tracer_identity = None
        self.worker = None
        self.privileged = False

    def sample(self):
        source = self.worker or identity(os.getpid())
        directory = cgroup_directory(source["pid"]) if source else None
        try:
            while True:
                if source is None or not same_process(source):
                    emit("unavailable", reason="memory-source-exited")
                    break
                emit("memory", source=source, scope="worker" if self.worker else "wrapper-only",
                     cgroup_path=str(directory) if directory else None,
                     **memory_sample(directory))
                if self.stop.wait(2):
                    break
        except Exception as error:
            emit("unavailable", reason="memory-sampler", error_type=type(error).__name__)

    def read_trace(self, process, worker):
        for line in process.stdout:
            if re.search(r"Process " + str(worker["pid"]) + r" attached", line):
                self.attached.set()
                emit("attached", worker_pid=worker["pid"], tracer_pid=process.pid)
            match = re.search(r"--- (SIG[A-Z0-9]+) \{(.*)\} ---", line)
            if match:
                fields = dict(re.findall(r"(si_code|si_pid|si_uid)=([A-Za-z0-9_-]+)", match[2]))
                tid = re.search(r"\[pid\s+(\d+)\]", line)
                emit("signal", signal=match[1], tracee_tid=int(tid[1]) if tid else None,
                     **fields)
        emit("tracer_exit", exit_code=process.wait(), attached=self.attached.is_set())

    def start_trace(self, worker, prefix):
        self.privileged = bool(prefix)
        command = prefix + ["strace", "-f", "-b", "execve", "-ttt", "-e", "trace=none",
                            "-e", "signal=" + SIGNALS, "-p", str(worker["pid"])]
        self.tracer = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       text=True, start_new_session=True)
        self.tracer_identity = identity(self.tracer.pid)
        self.reader = threading.Thread(target=self.read_trace, args=(self.tracer, worker), daemon=True)
        self.reader.start()
        self.attached.wait(0.5)
        return self.attached.is_set()

    def stop_trace(self, number):
        if not self.privileged:
            own_group(self.tracer, self.tracer_identity, number)
            return []
        if not same_process(self.tracer_identity):
            return []
        result = subprocess.run(["sudo", "-n", "--", sys.executable, "-B", str(Path(__file__).resolve()),
            "--stop-tracer", str(self.tracer.pid), str(self.tracer_identity["starttime"]), str(number)],
            capture_output=True, text=True, timeout=3)
        if result.returncode:
            emit("unavailable", reason="privileged-tracer-cleanup", exit_code=result.returncode)
            return []
        return json.loads(result.stdout)

    def finish_trace(self):
        process = self.tracer
        if process is None:
            return
        stopped = []
        if process.poll() is None:
            stopped += self.stop_trace(signal.SIGTERM)
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            stopped += self.stop_trace(signal.SIGKILL)
            process.wait(timeout=2)
        if self.reader is not None and self.reader.ident is not None:
            self.reader.join(timeout=2)
        reader_alive = self.reader.is_alive() if self.reader is not None else False
        if not reader_alive:
            process.stdout.close()
        emit("tracer_joined", pid=process.pid, stopped_tracer_pids=stopped,
             exit_code=process.returncode, reader_alive=reader_alive)
        self.tracer = self.reader = self.tracer_identity = None

    def start(self):
        self.worker = worker_ancestor()
        self.sampler = threading.Thread(target=self.sample, daemon=True)
        self.sampler.start()
        worker = self.worker
        if worker is None:
            emit("unavailable", reason="worker-ancestor-not-found")
        elif shutil.which("strace") is None:
            emit("unavailable", reason="strace-not-installed", worker=worker)
        else:
            emit("worker", **worker)
            if not self.start_trace(worker, []):
                self.finish_trace()
                if shutil.which("sudo") and same_process(worker):
                    self.start_trace(worker, ["sudo", "-n", "--"])
                if not self.attached.is_set():
                    emit("unavailable", reason="ptrace-or-strace-capability")

    def close(self):
        self.stop.set()
        if self.sampler is not None and self.sampler.ident is not None:
            self.sampler.join(timeout=3)
        self.finish_trace()
        emit("observers_joined", sampler_alive=self.sampler.is_alive() if self.sampler else False)


def observed(command):
    observer = Observer()
    child = child_identity = None
    interrupted = []

    def forward(number, _frame):
        interrupted.append(number)
        if child is not None:
            own_group(child, child_identity, number)

    old = {number: signal.signal(number, forward)
           for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    try:
        try:
            observer.start()
        except Exception as error:
            emit("unavailable", reason="observer-start", error_type=type(error).__name__)
        if interrupted:
            return 128 + interrupted[0]
        child = subprocess.Popen(command, start_new_session=True)
        child_identity = identity(child.pid)
        if interrupted:
            forward(interrupted[0], None)
        code = child.wait()
        return code if code >= 0 else 128 - code
    finally:
        try:
            observer.close()
        except Exception as error:
            emit("unavailable", reason="observer-close", error_type=type(error).__name__)
        for number, handler in old.items():
            signal.signal(number, handler)


def main():
    command = sys.argv[1:]
    if command[:1] == ["--stop-tracer"]:
        if len(command) != 4 or os.geteuid() != 0:
            return 64
        print(json.dumps(stop_privileged_tracer(*map(int, command[1:]))), flush=True)
        return 0
    if command[:1] == ["--"]:
        command.pop(0)
    if not command:
        return 64
    if os.environ.get("STRATALINT_RUNNER_DIAGNOSTICS") != "true":
        os.execvp(command[0], command)
    if sys.platform != "linux":
        emit("unavailable", reason="linux-only")
        os.execvp(command[0], command)
    return observed(command)


if __name__ == "__main__":
    raise SystemExit(main())
