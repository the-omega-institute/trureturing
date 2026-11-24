"""Drain earlier writers before pinning a protected dev generation."""

import base64
import json
import os
from pathlib import Path
import subprocess

WORKFLOW = ".github/workflows/lean-cache-publish.yml"
GROUP = "lean-cache-release-publisher"


def api(endpoint, *, pages=False):
    args = ["gh", "api"]
    if pages:
        args.extend(["--paginate", "--slurp"])
    args.append("repos/" + os.environ["GITHUB_REPOSITORY"] + "/" + endpoint)
    return json.loads(subprocess.check_output(args))


def drain():
    runs = {}
    # A run can advance from queued to in_progress during discovery.
    for state in ("requested", "waiting", "pending", "queued", "in_progress"):
        pages = api("actions/workflows/lean-cache-publish.yml/runs?per_page=100&status=" + state, pages=True)
        for page in pages:
            for run in page["workflow_runs"]:
                if str(run["id"]) != os.environ["GITHUB_RUN_ID"]:
                    runs[run["id"]] = run
    owners = {}
    for run in runs.values():
        sha = run["head_sha"]
        if sha not in owners:
            record = api("contents/" + WORKFLOW + "?ref=" + sha)
            definition = base64.b64decode(record["content"]).decode()
            # Ruby's standard YAML parser reads the actual version's workflow
            # group, including quotes, comments and inline mapping notation.
            owners[sha] = subprocess.check_output(
                ["ruby", "-ryaml", "-e", 'print YAML.safe_load(STDIN.read).dig("concurrency","group")'],
                input=definition, text=True,
            )
        if owners[sha] != GROUP:
            print(f"Awaiting legacy writer {run['id']} at {sha}", flush=True)
            subprocess.run(["gh", "run", "watch", str(run["id"]), "-R", os.environ["GITHUB_REPOSITORY"],
                            "--compact", "--interval", "60"], check=True)


def pin():
    run = os.environ["GITHUB_RUN_ID"]
    name = "generation-pin-" + run
    directory = Path(os.environ["RUNNER_TEMP"]) / "pin"
    directory.mkdir(exist_ok=True)
    file = directory / "source"
    artifacts = [item for page in api(f"actions/runs/{run}/artifacts?per_page=100", pages=True)
                 for item in page["artifacts"]]
    prior = [artifact for artifact in artifacts if artifact["name"] == name]
    if len(prior) > 1 or any(artifact["expired"] for artifact in prior):
        raise ValueError("expected a single unexpired source pin")
    branch = api("branches/dev")
    if not branch["protected"]:
        raise ValueError("dev must be protected")
    tip = branch["commit"]["sha"]
    if prior:
        subprocess.run(["gh", "run", "download", run, "-R", os.environ["GITHUB_REPOSITORY"],
                        "-n", name, "--dir", str(directory)], check=True)
        source = file.read_text().strip()
    else:
        if os.environ["GITHUB_RUN_ATTEMPT"] != "1":
            jobs = api(f"actions/runs/{run}/jobs?filter=all&per_page=100", pages=True)
            if artifacts or any(job["name"] == "pin" and job["conclusion"] == "success"
                                for page in jobs for job in page["jobs"]):
                raise ValueError("successful earlier work has lost its source pin")
        source = tip
    if len(source) != 40 or any(ch not in "0123456789abcdef" for ch in source):
        raise ValueError("invalid pinned commit")
    if source != tip:
        ancestor = subprocess.check_output(["gh", "api",
            f"repos/{os.environ['GITHUB_REPOSITORY']}/compare/{source}...{tip}?per_page=1",
            "--jq", ".merge_base_commit.sha"], text=True).strip()
        if ancestor != source:
            raise ValueError("pinned source is outside protected dev history")
    file.write_text(source + "\n")
    with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
        print(f"source={source}", file=output)
        print("upload=" + str(not prior).lower(), file=output)


if __name__ == "__main__":
    drain()
    pin()
