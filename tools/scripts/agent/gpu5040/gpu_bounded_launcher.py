#!/usr/bin/env python3
"""Run one resumed GPU round; exit 0 only to request launchd repetition."""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import stat
import subprocess
import sys
import uuid

from state_store import external_path, file_hash
from search_config import ANALYTIC_ALGORITHM, Config, descriptor, identity, protocol_initializer


class StopSignals:
    def __init__(self):
        self.number = None
        self.pending = None
        self.child = None
        self.forward_error = None
        self.finished = False
        for number in (signal.SIGTERM, signal.SIGINT):
            signal.signal(number, self.receive)

    def receive(self, number, frame):
        self.number = self.number or number
        self.pending = number
        if self.finished:
            raise SystemExit(128 + self.number)
        self.forward()

    def forward(self):
        if self.number is not None and self.child is not None:
            try:
                self.child.send_signal(self.pending)
            except ProcessLookupError:
                pass
            except OSError as error:
                self.forward_error = str(error)

    def finish(self):
        # Keep handlers through sys.exit, including a signal after result evaluation.
        self.finished = True
        if self.forward_error is not None:
            print("bounded GPU launcher: signal forwarding failed: " + self.forward_error,
                  file=sys.stderr, flush=True)
        if self.number is not None:
            raise SystemExit(128 + self.number)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nonnegative_integer(value):
    return type(value) is int and value >= 0


def checkpoint_identity(path):
    info = path.stat()
    require(stat.S_ISREG(info.st_mode) and info.st_size > 0, "latest.pt must be a nonempty file")
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def read_status(directory):
    value = json.loads((directory / "status.json").read_text())
    require(type(value) is dict, "status.json must contain an object")
    require(type(value.get("schema")) is int and value["schema"] == 2, "unsupported status schema")
    require(value.get("state_directory") == str(directory), "status state directory mismatch")
    require(value.get("latest_checkpoint") == str(directory / "latest.pt"), "status checkpoint path mismatch")
    require(value.get("error") is None, "status describes an error")
    require(value.get("phase") in ("running", "stopped"), "status phase is not resumable")
    config = value.get("config")
    require(type(config) is dict, "status config must be an object")
    # Same JSON encoding as gpu_worker.hash_json; no tensor runtime in this process.
    encoded = (json.dumps(config, sort_keys=True, indent=2, allow_nan=False) + "\n").encode("utf-8")
    require(hashlib.sha256(encoded).hexdigest() == value.get("config_sha256"), "status config hash mismatch")
    require(isinstance(value.get("source_sha256"), str) and bool(value["source_sha256"]),
            "missing status source hash")
    dimensions, seed_steps = config.get("dimensions"), config.get("seed_steps")
    require(type(dimensions) is list and bool(dimensions)
            and all(type(d) is int and d > 0 for d in dimensions), "invalid round dimensions")
    require(len(set(dimensions)) == len(dimensions), "duplicate round dimensions")
    require(type(seed_steps) is int and seed_steps > 0, "invalid round seed_steps")
    progress = value.get("progress")
    require(type(progress) is dict and all(nonnegative_integer(progress.get(key))
            for key in ("run_index", "iteration", "total_steps", "skipped_trials", "traversal_start_steps")),
            "invalid status progress")
    require(progress["iteration"] <= seed_steps and progress["skipped_trials"] <= progress["run_index"]
            and progress["total_steps"] - progress["traversal_start_steps"] ==
            (progress["run_index"] - progress["skipped_trials"]) * seed_steps + progress["iteration"],
            "inconsistent status progress")
    history = value.get("history_db")
    require(isinstance(history, str) and history == str(external_path(history)), "invalid history database path")
    if value.get("algorithm") == ANALYTIC_ALGORITHM:
        trial = value.get("trial")
        exhausted = value.get("phase") == "stopped" and value.get("stop_reason") == "exhausted"
        record = value.get("exhaustion") if exhausted else trial
        require(isinstance(record, dict), "missing analytic identity")
        spec = protocol_initializer(record.get("descriptor", {}), ANALYTIC_ALGORITHM)
        numeric = Config(**config)
        numeric.dimensions = tuple(numeric.dimensions)
        numeric.validate()
        expected = descriptor(numeric, 55, 0, value.get("runtime"), spec, value["source_sha256"])
        require(config["base_seed"] == 0 and record.get("descriptor") == expected
                and record.get("identity") == identity(expected), "analytic identity mismatch")
        completed = progress["run_index"] == 0 and progress["iteration"] == seed_steps
        skipped = (progress["run_index"] == 1 and progress["iteration"] == 0
                   and progress["skipped_trials"] == 1
                   and progress["total_steps"] == progress["traversal_start_steps"])
        require((exhausted and (completed or skipped)) or
                (not exhausted and progress["run_index"] == 0 and progress["iteration"] < seed_steps),
                "invalid analytic traversal")
        if trial is not None:
            require(trial.get("identity") == identity(expected) and trial.get("descriptor") == expected
                    and trial.get("terminal") is completed, "analytic trial mismatch")
        if value.get("checkpoint_saved") is False:
            require(exhausted and skipped and trial is None
                    and value.get("checkpoint_receipt") is None, "dishonest zero-update exhaustion")
            if (directory / "latest.pt").exists():
                retained = value.get("retained_checkpoint")
                checkpoint_identity(directory / "latest.pt")
                require(isinstance(retained, dict)
                        and retained.get("path") == str(directory / "latest.pt")
                        and retained.get("sha256") == file_hash(directory / "latest.pt")
                        and isinstance(retained.get("trial_identity"), str),
                        "retained checkpoint digest mismatch")
            else:
                require(value.get("retained_checkpoint") is None, "missing retained checkpoint")
            return value
    require(value.get("checkpoint_saved") is True,
            "status does not describe a saved, error-free checkpoint")
    receipt, session = value.get("checkpoint_receipt"), value.get("session")
    require(isinstance(receipt, dict) and isinstance(session, dict), "missing checkpoint/session receipt")
    require(isinstance(session.get("id"), str) and bool(session["id"])
            and receipt.get("session_id") == session["id"] and receipt.get("pid") == value.get("pid"),
            "checkpoint receipt invocation mismatch")
    require(isinstance(receipt.get("progress"), dict) and all(
        receipt["progress"].get(key) == progress[key] for key in
        ("run_index", "iteration", "total_steps", "skipped_trials", "traversal_start_steps")),
        "checkpoint receipt progress mismatch")
    checkpoint_identity(directory / "latest.pt")
    require(receipt.get("sha256") == file_hash(directory / "latest.pt"), "checkpoint digest mismatch")
    return value


def validate_completion(before, after, child_pid, max_steps, session_id):
    require(after.get("pid") == child_pid, "terminal status is not from this child")
    analytic = before.get("algorithm") == ANALYTIC_ALGORITHM
    expected_reason = "exhausted" if analytic else "max_steps"
    require(after["phase"] == "stopped" and after.get("stop_reason") == expected_reason,
            "child did not stop at " + expected_reason)
    if analytic:
        require(after.get("algorithm") == ANALYTIC_ALGORITHM
                and after["exhaustion"] == {key: before["trial"][key] for key in ("identity", "descriptor")},
                "child analytic identity changed")
    require(after["config_sha256"] == before["config_sha256"]
            and after["config"] == before["config"], "child config changed")
    require(after["source_sha256"] == before["source_sha256"], "child source changed")
    require(after["history_db"] == before["history_db"], "child history database changed")
    start = before["progress"]["total_steps"]
    require(after["progress"]["total_steps"] == start + max_steps,
            "terminal total_steps did not increase by exactly one round")
    session = after.get("session")
    require(type(session) is dict, "missing terminal session")
    require(session.get("id") == session_id, "terminal session is not this invocation")
    require(after["progress"]["traversal_start_steps"] == before["progress"]["traversal_start_steps"]
            and after["progress"]["skipped_trials"] >= before["progress"]["skipped_trials"],
            "child changed traversal accounting")
    require(nonnegative_integer(session.get("start_total_steps")) and session["start_total_steps"] == start,
            "child started from unexpected total_steps")
    require(nonnegative_integer(session.get("completed_steps")) and session["completed_steps"] == max_steps,
            "child completed an unexpected number of steps")
    resumed = session.get("resumed_from")
    require(type(resumed) is dict and all(nonnegative_integer(resumed.get(key))
            and resumed[key] == before["progress"][key]
            for key in ("run_index", "iteration", "total_steps")), "child resume origin mismatch")


def run_once(directory, stop, history_db=None):
    stop_path = directory / "STOP"
    if stop.number is not None or stop_path.exists():
        return 3
    before = read_status(directory)
    if history_db is not None:
        require(before["history_db"] == str(external_path(history_db)), "requested history database mismatch")
    analytic = before.get("algorithm") == ANALYTIC_ALGORITHM
    if analytic and before.get("stop_reason") == "exhausted":
        return 4
    previous_checkpoint = checkpoint_identity(directory / "latest.pt")
    config = before["config"]
    max_steps = (config["seed_steps"] - before["progress"]["iteration"] if analytic
                 else len(config["dimensions"]) * config["seed_steps"])
    worker = Path(__file__).resolve().with_name("gpu_worker.py")
    require(worker.is_file(), "adjacent gpu_worker.py is missing")
    session_id = uuid.uuid4().hex
    command = [sys.executable, "-B", str(worker), "--state-dir", str(directory), "--resume",
               "--history-db", before["history_db"], "--session-id", session_id,
               "--max-steps", str(max_steps), "--seed-steps", str(config["seed_steps"]),
               "--dimensions", ",".join(map(str, config["dimensions"]))]
    if analytic:
        runtime = before["runtime"]
        require(runtime.get("actual_device") in ("cpu", "mps:0"), "invalid analytic device")
        precision = runtime["training_precision"].removeprefix("torch.")
        require(precision in ("float32", "float64"), "invalid analytic precision")
        command += ["--device", runtime["actual_device"], "--precision", precision]
    # The last two flags are resume assertions: the worker rejects a config mismatch.
    if stop.number is not None or stop_path.exists():
        return 3
    child = subprocess.Popen(command)
    stop.child = child
    try:
        # A signal during Popen was latched before the child handle became available.
        stop.forward()
        returncode = child.wait()
    finally:
        if child.poll() is None:
            try:
                child.send_signal(signal.SIGTERM)
            finally:
                child.wait()
        stop.child = None
    if stop.number is not None or stop_path.exists():
        return 3
    require(returncode == 0, "worker exited with status " + str(returncode))
    after = read_status(directory)
    validate_completion(before, after, child.pid, max_steps, session_id)
    require(checkpoint_identity(directory / "latest.pt") != previous_checkpoint,
            "latest.pt was not freshly published")
    return 3 if stop_path.exists() or stop.number is not None else (4 if analytic else 0)


def main(argv=None):
    stop = StopSignals()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-dir", required=True)
    parser.add_argument("--history-db", help="assert the recorded external registry path")
    try:
        args = parser.parse_args(argv)
        return run_once(external_path(args.state_dir), stop, args.history_db)
    except Exception as error:
        print("bounded GPU launcher: " + str(error), file=sys.stderr, flush=True)
        return 1
    finally:
        stop.finish()


if __name__ == "__main__":
    sys.exit(main())
