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


def marker_source(kind):
    marker = "lean-modules-published" + ("-report" if kind == "report" else "")
    refs = api("git/matching-refs/heads/" + marker)
    matching = [row["object"]["sha"] for row in refs if row["ref"] == "refs/heads/" + marker]
    if not matching:
        return None
    source, = matching
    if not isinstance(source, str) or not re.fullmatch(r"[0-9a-f]{40}", source):
        raise ValueError("source_commit must be a lowercase 40-hex string")
    return source


def published_source(kind):
    source = marker_source(kind)
    if source is None:
        return None
    tip = protected_tip("dev")
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
    if kind == "compiler":
        # The existing compiler marker can still address a combined-format release at rollout.
        with tempfile.TemporaryDirectory(dir=os.environ["RUNNER_TEMP"]) as directory:
            subprocess.run(["gh", "release", "download", "lean-modules-" + source, "--repo",
                            os.environ["GITHUB_REPOSITORY"], "--pattern", "index.json",
                            "--dir", directory], check=True)
            index = json.loads((Path(directory) / "index.json").read_bytes())
        if (index.get("schema") != "lean-module-shards-v1" or index.get("source") != source
                or index.get("version") != "lean-modules-" + source):
            raise ValueError("compiler marker and index differ")
        if "kind" not in index:
            return None
        if index["kind"] != "compiler":
            raise ValueError("expected a published compiler index")
    return source


def pin(*, published=None, skip_published=None):
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
        source = published_source(published) if published else tip
        if source is None:
            with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
                print("source=\nupload=false", file=output)
            return
    if len(source) != 40 or any(ch not in "0123456789abcdef" for ch in source):
        raise ValueError("invalid pinned commit")
    if tip is not None and source != tip:
        ancestor = subprocess.check_output(["gh", "api",
            f"repos/{os.environ['GITHUB_REPOSITORY']}/compare/{source}...{tip}?per_page=1",
            "--jq", ".merge_base_commit.sha"], text=True).strip()
        if ancestor != source:
            raise ValueError("pinned source is outside protected dev history")
    marker = marker_source(skip_published) if skip_published else None
    status = None
    if marker and marker != source:
        status = api(f"compare/{marker}...{source}?per_page=1")["status"]
        if status not in ("ahead", "behind"):
            raise ValueError(f"{skip_published} marker and pinned source have incompatible histories: {status}")
    file.write_text(source + "\n")
    with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
        print(f"source={source}", file=output)
        print("upload=" + str(not prior).lower(), file=output)
        if marker == source:
            print("already_published=true", file=output)
        elif status == "behind":
            print("superseded=true", file=output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--published", choices=("compiler", "report"), help="pin the upstream publication")
    parser.add_argument("--skip-published", choices=("compiler", "report"), help="reuse the current publication")
    args = parser.parse_args()
    pin(published=args.published, skip_published=args.skip_published)
