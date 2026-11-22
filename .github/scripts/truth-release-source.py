"""Print the verified NAME=success inputs for a protected dev truth release."""

import json
import os
import re
import subprocess
import sys

REPOSITORY = "the-omega-institute/trureturing"
WORKFLOW = ".github/workflows/ci-current.yml"


def api(endpoint, *, pages=False):
    command = ["gh", "api", "--hostname", "github.com"]
    if pages:
        command += ["--paginate", "--slurp"]
    return json.loads(subprocess.check_output([*command, f"repos/{REPOSITORY}/{endpoint}"]))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(sha):
    branch = api("branches/dev")
    require(branch["protected"] and branch["protection"]["enabled"], "dev is unprotected")
    tip = branch["commit"]["sha"]
    if tip != sha:
        comparison = api(f"compare/{sha}...{tip}?per_page=1")
        require(comparison["merge_base_commit"]["sha"] == sha, f"{sha} is outside protected dev")

    policy = branch["protection"]["required_status_checks"]
    bindings = {(check["context"], check["app_id"]) for check in policy["checks"]}
    require(set(policy["contexts"]) == {name for name, _ in bindings},
            "inconsistent branch protection check contexts")
    for page in api("rules/branches/dev?per_page=100", pages=True):
        for rule in page:
            if rule["type"] == "required_status_checks":
                bindings.update((check["context"], check.get("integration_id"))
                                for check in rule["parameters"]["required_status_checks"])
    require(bindings, "no required check on protected dev")

    # Select the current attempt of the most recent push run for this exact commit.
    runs = api(f"actions/workflows/ci-current.yml/runs?branch=dev&event=push&head_sha={sha}&per_page=1")
    require(runs["workflow_runs"], f"missing dev push CI for {sha}")
    run = runs["workflow_runs"][0]
    require(run["head_sha"] == sha and run["head_branch"] == "dev" and run["event"] == "push"
            and run["path"] == WORKFLOW and run["head_repository"]["full_name"] == REPOSITORY
            and run["status"] == "completed" and run["conclusion"] == "success",
            f"dev push CI run {run['id']} for {sha} has no successful conclusion")
    run_id, attempt = run["id"], run["run_attempt"]
    job_pages = api(f"actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100", pages=True)
    jobs = [job for page in job_pages for job in page["jobs"]]
    for name in sorted({name for name, _ in bindings}):
        require(name and "=" not in name and name.isprintable(), f"unsupported check name {name!r}")
        matches = [job for job in jobs if job["name"] == name]
        require(len(matches) == 1, f"expected one {name!r} job in run {run_id} attempt {attempt}")
        job = matches[0]
        require(job["head_sha"] == sha and job["status"] == "completed" and job["conclusion"] == "success",
                f"required job {name!r} did not succeed on {sha}")
        check = api(f"check-runs/{job['id']}")
        require(check["head_sha"] == sha and check["name"] == name and check["status"] == "completed"
                and check["conclusion"] == "success" and check["check_suite"]["id"] == run["check_suite_id"]
                and all(app in (None, -1, check["app"]["id"]) for context, app in bindings if context == name),
                f"required check {name!r} does not match its protected app and CI run")
    print(f"Verified https://github.com/{REPOSITORY}/actions/runs/{run_id}/attempts/{attempt}",
          file=sys.stderr)
    return sorted({name for name, _ in bindings})


def main():
    sha = os.environ["GITHUB_SHA"]
    require(os.environ["GITHUB_REPOSITORY"] == REPOSITORY and os.environ["GITHUB_REF"] == "refs/heads/dev",
            "expected the official dev workflow")
    require(re.fullmatch(r"[0-9a-f]{40}", sha)
            and subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == sha,
            "checkout does not match the event SHA")
    for name in verify(sha):
        print(f"{name}=success")


if __name__ == "__main__":
    try:
        main()
    except (KeyError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"TRUTH_RELEASE_SOURCE_REJECTED {error}")
