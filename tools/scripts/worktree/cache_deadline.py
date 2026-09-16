"""One optional cache window inside an existing Actions job deadline.

The job limit is an explicit workflow input, never inferred from workflow text.
The fixed run/attempt's job metadata establishes the start. Subsequent layers
read the same local window and use monotonic time; unavailable metadata disables
cache writes without changing any check or required-artifact result.
"""
import argparse
import json
import math
import os
import pathlib
import re
import subprocess
import tempfile
import time
from datetime import datetime

# Optional transport boundaries: keep the existing job limit and leave time for
# diagnostics and runner cleanup. A snapshot also leaves one minute for its save.
CLEANUP_SECONDS = 120
SAVE_START_SECONDS = 5
SAVE_MINIMUM_SECONDS = 60
METADATA_TIMEOUT_SECONDS = 15
STAGES = ("build", "engineering", "current")


class CacheDeadline:
    def __init__(self, cutoff=None, reason="unavailable", monotonic=None):
        self.cutoff = cutoff
        self.reason = reason
        self.clock = monotonic or time.monotonic

    def remaining(self):
        if self.cutoff is None:
            return 0
        value = self.cutoff - self.clock()
        return max(0, value) if math.isfinite(value) else 0

    def snapshot_seconds(self):
        return max(0, self.remaining() - SAVE_MINIMUM_SECONDS - SAVE_START_SECONDS)

    def save_timeout_minutes(self, maximum=12):
        if type(maximum) is not int or maximum < 1:
            return 0
        return min(maximum, max(0, math.floor((self.remaining() - SAVE_START_SECONDS) / 60)))


def identity(stage, env):
    if stage not in STAGES or env.get("GITHUB_JOB") != stage:
        raise ValueError("cache job identity mismatch")
    if env.get("GITHUB_EVENT_NAME") != "push" or env.get("STRATALINT_CACHE_WRITES") != "true":
        raise ValueError("cache writes disabled")
    repository = env.get("GITHUB_REPOSITORY", "")
    commit = env.get("CANDIDATE_SHA", "")
    run, attempt = env.get("GITHUB_RUN_ID", ""), env.get("GITHUB_RUN_ATTEMPT", "")
    if (not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)
            or not re.fullmatch(r"[0-9a-f]{40}", commit) or commit == "0" * 40
            or commit != env.get("GITHUB_SHA")
            or not all(re.fullmatch(r"[1-9][0-9]*", value) for value in (run, attempt))):
        raise ValueError("cache run identity mismatch")
    return {"stage": stage, "repository": repository, "run_id": run, "run_attempt": attempt,
            "candidate": commit, "runner_name": env.get("RUNNER_NAME", "")}


def state_path(root, stage):
    if stage not in STAGES:
        raise ValueError("invalid cache stage")
    return pathlib.Path(root) / "build/ci" / ("cache-deadline-" + stage + ".json")


def query_jobs(repository, run_id, attempt, env, *, run=None):
    result = (run or subprocess.run)(
        ["gh", "api", "repos/" + repository + "/actions/runs/" + run_id
         + "/attempts/" + attempt + "/jobs?per_page=100"],
        env=dict(env), capture_output=True, text=True, check=True, timeout=METADATA_TIMEOUT_SECONDS)
    return json.loads(result.stdout)


def begin(root, stage, job_timeout_minutes, *, env=None, fetch_jobs=None, now=None, monotonic=None):
    env = os.environ if env is None else env
    clock = monotonic or time.monotonic
    try:
        path = state_path(root, stage)
        # Failed initialization must never leave a previously usable window.
        path.unlink(missing_ok=True)
        expected = identity(stage, env)
        if type(job_timeout_minutes) is not int or not 1 <= job_timeout_minutes <= 60:
            raise ValueError("invalid explicit job timeout")
        query = fetch_jobs or query_jobs
        response = query(expected["repository"], expected["run_id"], expected["run_attempt"], env)
        if (not isinstance(response, dict) or not isinstance(response.get("jobs"), list)
                or type(response.get("total_count")) is not int
                or response["total_count"] != len(response["jobs"])
                or not all(isinstance(job, dict) for job in response["jobs"])):
            raise ValueError("incomplete cache job metadata")
        matching = [job for job in response["jobs"] if job.get("name") == stage]
        if len(matching) != 1:
            raise ValueError("cache job is absent or ambiguous")
        job = matching[0]
        if (type(job.get("id")) is not int or job["id"] < 1
                or type(job.get("run_id")) is not int or job["run_id"] != int(expected["run_id"])
                or type(job.get("run_attempt")) is not int or job["run_attempt"] != int(expected["run_attempt"])
                or job.get("head_sha") != expected["candidate"] or job.get("status") != "in_progress"
                or expected["runner_name"] and job.get("runner_name") != expected["runner_name"]):
            raise ValueError("cache job metadata identity mismatch")
        started = job.get("started_at")
        if not isinstance(started, str) or not re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", started):
            raise ValueError("invalid cache job start")
        epoch = datetime.fromisoformat(started.replace("Z", "+00:00")).timestamp()
        wall, sampled = (now or time.time)(), clock()
        if not all(math.isfinite(value) for value in (epoch, wall, sampled)) or epoch > wall:
            raise ValueError("cache job start is in the future")
        remaining = epoch + job_timeout_minutes * 60 - CLEANUP_SECONDS - wall
        record = {"schema": "ci-cache-deadline-v1", **expected, "job_id": job["id"],
                  "started_at": started, "job_timeout_minutes": job_timeout_minutes,
                  "sampled_monotonic": sampled, "cutoff_monotonic": sampled + remaining}
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, prefix=".cache-deadline-", delete=False) as stream:
            temporary = pathlib.Path(stream.name)
            try:
                json.dump(record, stream, sort_keys=True)
                stream.write("\n")
                stream.flush()
                os.replace(temporary, path)
            finally:
                temporary.unlink(missing_ok=True)
        return CacheDeadline(record["cutoff_monotonic"], "available", clock)
    except (OSError, ValueError, KeyError, TypeError, OverflowError, subprocess.SubprocessError):
        # HTTP/tool stderr can contain credentials; expose a fixed reason only.
        return CacheDeadline(reason="job-metadata-unavailable", monotonic=clock)


def load_deadline(root, stage, *, env=None, monotonic=None):
    clock = monotonic or time.monotonic
    try:
        expected = identity(stage, os.environ if env is None else env)
        record = json.loads(state_path(root, stage).read_text())
        if (not isinstance(record, dict) or record.get("schema") != "ci-cache-deadline-v1"
                or any(record.get(key) != value for key, value in expected.items())
                or type(record.get("job_id")) is not int or record["job_id"] < 1
                or type(record.get("job_timeout_minutes")) is not int
                or not 1 <= record["job_timeout_minutes"] <= 60):
            raise ValueError("cache deadline identity mismatch")
        if not isinstance(record.get("started_at"), str):
            raise ValueError("invalid cache job start")
        start = datetime.fromisoformat(record["started_at"].replace("Z", "+00:00"))
        if start.tzinfo is None:
            raise ValueError("cache job start has no timezone")
        sampled, cutoff = record["sampled_monotonic"], record["cutoff_monotonic"]
        if (any(type(value) not in (int, float) or not math.isfinite(value) for value in (sampled, cutoff))
                or clock() < sampled or cutoff > sampled + record["job_timeout_minutes"] * 60 - CLEANUP_SECONDS):
            raise ValueError("invalid cache deadline clock")
        return CacheDeadline(cutoff, "available", clock)
    except (OSError, ValueError, KeyError, TypeError, OverflowError):
        return CacheDeadline(reason="deadline-state-unavailable", monotonic=clock)


def save_outputs(window, maximum=12):
    minutes = window.save_timeout_minutes(maximum)
    # Actions validates timeout inputs even for skipped steps; never output zero.
    return {"save_allowed": minutes > 0, "save_timeout_minutes": minutes or 1}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("begin", "allow-save"))
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--stage", choices=STAGES, required=True)
    parser.add_argument("--job-timeout-minutes", type=int)
    parser.add_argument("--max-minutes", type=int, default=12)
    args = parser.parse_args()
    if args.command == "begin":
        window = begin(args.repository, args.stage, args.job_timeout_minutes)
        values = {"cache_allowed": window.save_timeout_minutes() > 0}
    else:
        window = load_deadline(args.repository, args.stage)
        values = save_outputs(window, args.max_minutes)
    print("CI_CACHE_DEADLINE " + json.dumps({"stage": args.stage, "reason": window.reason,
          "remaining_seconds": round(window.remaining(), 3), **values}, sort_keys=True))
    try:
        if os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
                for key, value in values.items():
                    stream.write(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n")
    except OSError:
        print("CI_CACHE_DEADLINE outputs-unavailable")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
