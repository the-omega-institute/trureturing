"""Short subprocess fixture. No tensor imports and no access to live state."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import sys


def publish(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + "\n").encode()


parser = argparse.ArgumentParser()
parser.add_argument("--state-dir", required=True)
parser.add_argument("--resume", action="store_true", required=True)
parser.add_argument("--max-steps", type=int, required=True)
parser.add_argument("--seed-steps", type=int, required=True)
parser.add_argument("--dimensions", required=True)
parser.add_argument("--history-db", required=True)
parser.add_argument("--session-id", required=True)
parser.add_argument("--device")
parser.add_argument("--precision")
args = parser.parse_args()
state = Path(args.state_dir)
options = json.loads((state / "fixture-options.json").read_text())
scenario = options["scenario"]
lock = open(state.parent / ".gpu-worker.lock", "a+b")
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    print("fixture: worker lock held", file=sys.stderr)
    sys.exit(2)

before = json.loads((state / "status.json").read_text())
assert args.history_db == before["history_db"]
assert args.seed_steps == before["config"]["seed_steps"]
assert args.dimensions == ",".join(map(str, before["config"]["dimensions"]))
publish(state / "child-started.json", encode({"pid": os.getpid(), "argv": sys.argv,
                                             "executable": sys.executable}))
received = None


def on_signal(number, frame):
    global received
    received = signal.Signals(number).name
    print("SIGNAL " + received, flush=True)


for number in (signal.SIGTERM, signal.SIGINT):
    signal.signal(number, on_signal)

if options.get("barrier"):
    print("READY", flush=True)
    assert sys.stdin.readline().strip() == "release"

if scenario == "failure":
    sys.exit(7)
if scenario == "stale":
    sys.exit(0)
if scenario == "malformed":
    publish(state / "status.json", b"{broken")
    sys.exit(0)
if scenario == "missing_status":
    (state / "status.json").unlink()
    sys.exit(0)

start = before["progress"]["total_steps"]
completed = args.max_steps if scenario != "stop" and received is None else 1
total = start + completed
seed_steps = args.seed_steps
# The worker leaves iteration == seed_steps at an exact seed boundary.
run_index, remainder = divmod(total - before["progress"]["traversal_start_steps"], seed_steps)
iteration = remainder
if remainder == 0 and total:
    run_index -= 1
    iteration = seed_steps
skipped = before["progress"]["skipped_trials"] + options.get("skipped_work", 0)
run_index += skipped
status = dict(before)
status.update(pid=os.getpid(), phase="stopped", stop_reason="max_steps", error=None,
              checkpoint_saved=True)
status["progress"] = dict(before["progress"], total_steps=total, run_index=run_index,
                          iteration=iteration, skipped_trials=skipped)
if before.get("trial") is not None:
    status["trial"] = dict(before["trial"], terminal=iteration == seed_steps)
    assert args.device == before["runtime"]["actual_device"]
    assert "torch." + args.precision == before["runtime"]["training_precision"]
status["session"] = {
    "id": args.session_id,
    "start_total_steps": start, "completed_steps": completed,
    "resumed_from": {key: before["progress"][key]
                     for key in ("run_index", "iteration", "total_steps")},
}
if scenario == "stop":
    status["stop_reason"] = "STOP"
if received:
    status["stop_reason"] = received
if scenario == "changed_config":
    status["config"] = dict(status["config"], base_seed=99)
    status["config_sha256"] = hashlib.sha256(encode(status["config"])).hexdigest()
status.update(options.get("terminal_patch", {}))
if scenario != "no_checkpoint":
    publish(state / "latest.pt", b"fixture checkpoint " + str(total).encode())
if scenario == "missing_checkpoint":
    (state / "latest.pt").unlink()
if scenario == "empty_checkpoint":
    publish(state / "latest.pt", b"")
status["checkpoint_receipt"] = {
    "session_id": args.session_id, "pid": os.getpid(), "progress": status["progress"],
    "sha256": hashlib.sha256((state / "latest.pt").read_bytes()).hexdigest()
    if (state / "latest.pt").exists() else None,
}
status["checkpoint_receipt"].update(options.get("receipt_patch", {}))
publish(state / "status.json", encode(status))
if options.get("terminal_barrier"):
    print("TERMINAL", flush=True)
    assert sys.stdin.readline().strip() == "release"
print("CHILD_EXIT", flush=True)
sys.exit(7 if scenario == "failure_after_status" else 0)
