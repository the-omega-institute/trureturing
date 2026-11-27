"""Dispatch verified compiler units and physical shards for one pinned publication."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.parse import urlencode
import zipfile


WORKFLOW = "ci-lean-generation-compile.yml"
CACHE_TOOL = "tools/scripts/worktree/lean_module_cache.py"
SHA = re.compile(r"[0-9a-f]{40}")
DIGEST = re.compile(r"[0-9a-f]{64}")


def read(path):
    return json.loads(path.read_bytes())


def positive(value):
    number = int(value)
    if number < 1:
        raise ValueError("expected a positive integer")
    return number


def valid_ids(values, valid):
    return isinstance(values, list) and all(valid(v) for v in values) and len(values) == len(set(values))


def validate_receipts(plan, receipts):
    units = plan["compiler_dag"]["units"]
    if not isinstance(receipts, dict):
        raise ValueError("compiler receipts must be keyed by unit")
    for key, row in receipts.items():
        unit = units.get(key)
        if not unit or not isinstance(row, dict) or any(
                row.get(field) != unit[field] for field in ("key", "asset", "fingerprint", "members", "artifact_kind")):
            raise ValueError(f"receipt does not match planned unit {key}")
        if (type(row.get("bytes")) is not int or row["bytes"] <= 0 or not isinstance(row.get("sha256"), str)
                or not DIGEST.fullmatch(row["sha256"]) or not isinstance(row.get("version"), str)
                or not row["version"]):
            raise ValueError(f"missing compiler artifact identity for {key}")


class Schedule:
    def __init__(self, plan, pending, receipts):
        self.units = plan["compiler_dag"]["units"]
        self.plan = plan
        self.done = set(receipts)
        validate_receipts(plan, receipts)
        keys, lanes = pending["units"], pending["lanes"]
        if not valid_ids(keys, lambda k: isinstance(k, str) and k in self.units and DIGEST.fullmatch(k)):
            raise ValueError("unknown or duplicate pending compiler unit")
        if not valid_ids(lanes, lambda n: type(n) is int and 0 <= n < len(plan["lanes"])):
            raise ValueError("unknown or duplicate pending physical lane")
        self.waiting = set(keys) - self.done
        self.lanes = set(lanes)
        self.lane_units = pending["lane_units"]
        if set(self.lane_units) != {str(n) for n in lanes}:
            raise ValueError("missing or unexpected physical lane dependency list")
        known = set(keys) | self.done
        for dependencies in [self.units[key]["deps"] for key in keys] + list(self.lane_units.values()):
            if not valid_ids(dependencies, lambda key: isinstance(key, str) and key in known):
                raise ValueError("physical plan omits a compiler prerequisite")

    def take(self, unit_size, shard_size):
        ready = sorted(n for n in self.lanes if self.done.issuperset(self.lane_units[str(n)]))
        if ready:
            selected = ready[:shard_size]
            self.lanes.difference_update(selected)
            return "shards", selected
        ready = (key for key in self.waiting if self.done.issuperset(self.units[key]["deps"]))
        selected = sorted(ready, key=lambda key: (-self.units[key]["rank"], key))[:unit_size]
        if selected:
            self.waiting.difference_update(selected)
            return "units", selected
        return None

    def accept(self, phase, assignment, result):
        if phase == "shards":
            if result != {"lanes": assignment} or not valid_ids(result["lanes"], lambda n: type(n) is int):
                raise ValueError("incomplete or unexpected physical shard result")
            return
        if not isinstance(result, dict) or set(result) != set(assignment):
            raise ValueError("incomplete or unexpected compiler unit result")
        validate_receipts(self.plan, result)
        self.done.update(result)


def run_id(response):
    if not isinstance(response, dict):
        return None
    identifier = response.get("workflow_run_id", response.get("run_id", response.get("id")))
    return identifier if type(identifier) is int and identifier > 0 else None


class GitHub:
    def __init__(self, source):
        self.repo = os.environ["GITHUB_REPOSITORY"]
        self.parent = str(positive(os.environ["GITHUB_RUN_ID"]))
        self.attempt = str(positive(os.environ["GITHUB_RUN_ATTEMPT"]))
        self.source = source
        self.path = f"actions/workflows/{WORKFLOW}"
        self.workflow_id = self.json(self.path)["id"]
        self.last_dispatch = 0.0

    def api(self, endpoint, *, payload=None, pages=False):
        command = ["gh", "api", "--allow-escape-sequences"]
        if pages:
            command.extend(["--paginate", "--slurp"])
        if payload is not None:
            command.extend(["--method", "POST", "--input", "-"])
        command.append(f"repos/{self.repo}/{endpoint}")
        data = json.dumps(payload).encode() if payload is not None else None
        for attempt in range(4):
            try:
                result = subprocess.run(command, input=data, capture_output=True, timeout=120)
            except subprocess.TimeoutExpired:
                if payload is not None or attempt == 3:
                    raise
                time.sleep(2 ** attempt)
                continue
            if not result.returncode:
                return result.stdout
            message = result.stderr.decode(errors="replace").strip()
            limited = "HTTP 429" in message or ("HTTP 403" in message and "rate limit" in message.lower())
            temporary = any(f"HTTP {code}" in message for code in (404, 500, 502, 503, 504)) or any(
                reason in message.lower() for reason in ("timed out", "connection reset", "unexpected eof", "tls handshake"))
            if attempt == 3 or not (limited or (temporary and payload is None)):
                raise RuntimeError(f"GitHub {endpoint}: {message}")
            time.sleep(60 if limited else 2 ** attempt)
        raise AssertionError("unreachable")

    def json(self, endpoint, **options):
        data = self.api(endpoint, **options)
        return json.loads(data) if data.strip() else None

    def runs(self, created, *, all_pages=True):
        filters = {"event": "workflow_dispatch", "branch": "dev", "per_page": 100}
        if created:
            filters["created"] = ">=" + created
        endpoint = self.path + "/runs?" + urlencode(filters)
        pages = self.json(endpoint, pages=True) if all_pages else [self.json(endpoint)]
        return [run for page in pages for run in page["workflow_runs"]]

    def title(self, batch, phase):
        return f"Compiler release {self.parent}/{self.attempt}/{batch} {phase}"

    def matches(self, row, title):
        return (row.get("workflow_id") == self.workflow_id and row.get("display_title") == title
                and row.get("actor", {}).get("login") == "github-actions[bot]"
                and row.get("event") == "workflow_dispatch" and row.get("head_branch") == "dev"
                and row.get("repository", {}).get("full_name") == self.repo
                and row.get("head_repository", {}).get("full_name") == self.repo)

    def dispatch(self, batch, phase, assignment):
        time.sleep(max(0, self.last_dispatch + 1.0 - time.monotonic()))
        self.last_dispatch = time.monotonic()
        title = self.title(batch, phase)
        since = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 60))
        inputs = dict(parent_run=self.parent, parent_attempt=self.attempt, source=self.source,
                      batch=str(batch), phase=phase, assignment=json.dumps(assignment, separators=(",", ":")))
        payload = dict(ref="dev", inputs=inputs, return_run_details=True)
        try:
            identifier = run_id(self.json(self.path + "/dispatches", payload=payload))
            if identifier:
                return identifier
        except (RuntimeError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
            print(f"Recovering dispatch {title} after {error}", file=sys.stderr, flush=True)
        # A lost response or a successful 204 must not dispatch the assignment a second time.
        for delay in (1, 4, 10, 20, 40):
            time.sleep(delay)
            matches = [row["id"] for row in self.runs(since) if self.matches(row, title)]
            if len(matches) == 1:
                return matches[0]
            if matches:
                raise ValueError("multiple workflow runs match dispatch " + title)
        raise RuntimeError("cannot identify the child run for " + title)

    def result(self, identifier, batch):
        name = f"compiler-result-{self.attempt}-{batch}"
        endpoint = f"actions/runs/{identifier}/artifacts?" + urlencode({"name": name})
        for delay in (0, 2, 4, 8):
            if delay:
                time.sleep(delay)
            artifacts = [a for a in self.json(endpoint)["artifacts"] if a["name"] == name]
            if artifacts:
                break
        if len(artifacts) != 1 or artifacts[0]["expired"]:
            raise ValueError(f"child {identifier} has no unique live result artifact")
        if "workflow_run" in artifacts[0] and artifacts[0]["workflow_run"].get("id") != identifier:
            raise ValueError(f"child {identifier} has no unique result artifact")
        artifact = artifacts[0]
        raw = self.api(f"actions/artifacts/{artifact['id']}/zip")
        if artifact.get("digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            raise ValueError("child result archive digest differs")
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            if archive.namelist() != ["result.json"]:
                raise ValueError("unexpected child result archive contents")
            return json.loads(archive.read("result.json"))


def coordinate(github, schedule, maximum, unit_size, shard_size, refresh=None):
    # GitHub limits the combined workflow_dispatch input payload to 65,535 characters.
    # Unit keys are 64 hexadecimal characters. Keep room for the pinned source and run IDs.
    unit_size = min(unit_size, 950)
    shard_size = min(shard_size, 4000)
    active = {}
    oldest = {}
    failures = {}
    serial = 0
    while schedule.waiting or schedule.lanes or active:
        # Interleave dispatch and completion handling on wide frontiers.
        sent = 0
        for _ in range(20):
            if maximum is not None and len(active) >= maximum:
                break
            assignment = schedule.take(unit_size, shard_size)
            if not assignment:
                break
            phase, values = assignment
            serial += 1
            since = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 60))
            identifier = github.dispatch(serial, phase, values)
            if identifier in active:
                raise ValueError("multiple assignments resolved to the same workflow run")
            active[identifier] = (serial, phase, values)
            oldest[identifier] = since
            sent += 1
            print(f"Dispatched compiler {phase} batch {serial}: {len(values)} inputs, run {identifier}", flush=True)
        if not active:
            raise ValueError("compiler dependencies do not admit a ready batch")
        recent = {row["id"]: row for row in github.runs(min(oldest.values()), all_pages=len(active) > 80)}
        completed = False
        for identifier, (batch, phase, values) in list(active.items()):
            row = recent.get(identifier) or github.json(f"actions/runs/{identifier}")
            if not github.matches(row, github.title(batch, phase)):
                raise ValueError(f"untrusted compiler workflow run {identifier}")
            if row["status"] != "completed":
                continue
            if row["conclusion"] == "success":
                schedule.accept(phase, values, github.result(identifier, batch))
            else:
                outstanding = set(values)
                if refresh:
                    receipts, pending = refresh(phase)
                    if phase == "units":
                        validate_receipts(schedule.plan, receipts)
                        recovered = outstanding.intersection(receipts)
                        schedule.done.update(recovered)
                        outstanding.difference_update(recovered)
                    else:
                        outstanding.intersection_update(pending["lanes"])
                for value in sorted(outstanding):
                    attempts = failures.setdefault((phase, value), [])
                    attempts.append(identifier)
                    if len(attempts) >= 3:
                        raise RuntimeError(f"compiler {phase} batch {batch} ended {row['conclusion']}; "
                                           f"child runs {attempts}; remaining inputs {sorted(outstanding)}")
                if phase == "units":
                    schedule.waiting.update(outstanding)
                else:
                    schedule.lanes.update(outstanding)
                print(f"Compiler run {identifier} ended {row['conclusion']}; "
                      f"{len(outstanding)} of {len(values)} inputs remain", file=sys.stderr, flush=True)
            del active[identifier]
            del oldest[identifier]
            completed = True
        if not completed and sent < 20:
            time.sleep(30)


def cache(operation, plan, output, *options):
    subprocess.run([sys.executable, CACHE_TOOL, operation, "--plan", str(plan),
                    "--output", str(output), *map(str, options)], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--pending", type=Path)
    parser.add_argument("--max-active", type=positive)
    parser.add_argument("--units-per-batch", type=positive, default=8)
    parser.add_argument("--shards-per-batch", type=positive, default=1)
    args = parser.parse_args()
    if args.prepare_only:
        if not args.directory or args.pending:
            parser.error("--prepare-only requires --directory")
        args.directory.mkdir(parents=True, exist_ok=True)
        cache("compiler-pending-shards", args.plan, args.directory / "pending.json",
              "--resume-plan", args.directory / "module-plan.json")
        return
    if args.directory or not args.pending:
        parser.error("dispatch requires --pending")
    plan = read(args.plan)
    source = plan["source"]
    if plan.get("kind") != "compiler" or not SHA.fullmatch(source) or plan["version"] != f"lean-modules-{source}":
        raise ValueError("invalid pinned compiler release")
    with tempfile.TemporaryDirectory() as directory:
        receipts = Path(directory) / "receipts.json"
        cache("compiler-receipts", args.plan, receipts)
        schedule = Schedule(plan, read(args.pending), read(receipts))

        def refresh(phase):
            if phase == "units":
                cache("compiler-receipts", args.plan, receipts)
                return read(receipts), None
            pending = Path(directory) / "pending.json"
            cache("compiler-pending-shards", args.plan, pending)
            return None, read(pending)

        if schedule.waiting or schedule.lanes:
            coordinate(GitHub(source), schedule, args.max_active, args.units_per_batch, args.shards_per_batch, refresh)


if __name__ == "__main__":
    main()
