"""Pin a protected dev commit for this publication and its retries."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


def api(endpoint, *, pages=False):
    args = ["gh", "api"]
    if pages:
        args.extend(["--paginate", "--slurp"])
    args.append("repos/" + os.environ["GITHUB_REPOSITORY"] + "/" + endpoint)
    return json.loads(subprocess.check_output(args))


def protected_tip(name):
    branch = api("branches/" + name)
    if not branch["protected"]:
        raise ValueError(f"{name} must be protected")
    return branch["commit"]["sha"]


def published_source():
    payload = {}
    if os.environ["GITHUB_EVENT_NAME"] == "repository_dispatch":
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
        payload = event.get("client_payload")
        if payload is None:
            payload = {}
        if not isinstance(payload, dict):
            raise ValueError("client_payload must be a JSON object")
    if "source_commit" in payload:
        source = payload["source_commit"]
        tip = os.environ["GITHUB_SHA"]
    else:
        source = api("git/ref/heads/lean-modules-published")["object"]["sha"]
        tip = protected_tip("dev")
    if not isinstance(source, str) or not re.fullmatch(r"[0-9a-f]{40}", source):
        raise ValueError("source_commit must be a lowercase 40-hex string")
    if source != tip:
        comparison = api(f"compare/{source}...{tip}?per_page=1")
        ahead = comparison["ahead_by"]
        error = "source_commit must be on the first-parent history of protected dev"
        if comparison["merge_base_commit"]["sha"] != source or type(ahead) is not int or ahead < 1:
            raise ValueError(error)

        # All commits ahead of source bound the length of a first-parent walk to it.
        url = f"{os.environ['GITHUB_SERVER_URL']}/{os.environ['GITHUB_REPOSITORY']}.git"
        with tempfile.TemporaryDirectory(dir=os.environ["RUNNER_TEMP"]) as history:
            subprocess.run(["git", "init", "--bare", "--quiet", history], check=True)
            subprocess.run([
                "git", "-C", history, "fetch", "--no-tags", "--filter=tree:0", f"--depth={ahead + 1}", url, tip,
            ], check=True)
            first_parents = subprocess.check_output([
                "git", "-C", history, "rev-list", "--first-parent", tip,
            ], text=True).splitlines()
        if source not in first_parents:
            raise ValueError(error)
    return source


def pin(*, published=False):
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
    tip = None if published else protected_tip("dev")
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
        source = published_source() if published else tip
    if len(source) != 40 or any(ch not in "0123456789abcdef" for ch in source):
        raise ValueError("invalid pinned commit")
    if tip is not None and source != tip:
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--published", action="store_true", help="pin the Truth Release source")
    pin(published=parser.parse_args().published)
