"""Read-only, perishable review eligibility for the upstream ci-pr workflow.

Only GitHub GET requests are made. This is deliberately not a generic CI engine,
merge gate, workflow executor, or assertion of mathematical correctness.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
from urllib.parse import quote, urlencode
import uuid

SCHEMA = "contribution-queue.v1"
DEFAULT_REPO = "the-omega-institute/trureturing"
WORKFLOW = ".github/workflows/ci-pr.yml"
ACTIONS_APP = 15368  # GitHub.com's platform app, not an author identity.


class QueueError(Exception):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def positive(value):
    return type(value) is int and value > 0


def sha(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None


def reason(code, **details):
    return {"code": code, **details}


class GitHub:
    """Small JSON transport: fixed host, argv only, fresh requests, full pagination."""

    def get(self, path, **params):
        if not path.startswith("/") or "?" in path or "#" in path:
            raise QueueError("invalid_endpoint", "Expected a fixed GitHub API path")
        query = urlencode({**params, "_cq_observation": uuid.uuid4().hex})
        argv = ["gh", "api", "--hostname", "github.com", "--method", "GET",
                "-H", "Accept: application/vnd.github+json", "-H", "X-GitHub-Api-Version: 2022-11-28",
                "-H", "Cache-Control: no-cache", path + "?" + query]
        try:
            proc = subprocess.run(argv, capture_output=True, text=True, timeout=90, check=False)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise QueueError("api_unavailable", f"GitHub GET unavailable: {path}; check gh authentication/network") from exc
        if proc.returncode:
            # Never forward response bodies, token diagnostics or untrusted prose.
            raise QueueError("api_error", f"GitHub GET failed: {path}; check repository, Members/read:org, Actions, Checks and Administration read rights")
        try:
            return json.loads(proc.stdout)
        except (ValueError, TypeError) as exc:
            raise QueueError("invalid_api_response", f"GitHub GET returned invalid JSON: {path}") from exc

    def pages(self, path, key=None, **params):
        rows, seen, expected = [], set(), None
        page = 1
        while True:
            data = self.get(path, per_page=100, page=page, **params)
            batch = data.get(key) if key and isinstance(data, dict) else data
            if not isinstance(batch, list) or any(not isinstance(r, dict) for r in batch):
                raise QueueError("invalid_api_response", f"Expected a list from {path}")
            if key:
                count = data.get("total_count")
                if type(count) is not int or count < 0 or (expected is not None and count != expected):
                    raise QueueError("pagination_changed", f"List count missing or changed: {path}; retry scan")
                expected = count
            for row in batch:
                identity = row.get("id", row.get("login", row.get("number", fingerprint(row))))
                if identity in seen:
                    raise QueueError("pagination_changed", f"Duplicate item while paginating {path}; retry scan")
                seen.add(identity)
            rows.extend(batch)
            if expected is not None and len(rows) > expected:
                raise QueueError("pagination_changed", f"List grew while paginating {path}; retry scan")
            if len(batch) < 100:
                if expected is not None and len(rows) != expected:
                    raise QueueError("pagination_incomplete", f"Incomplete list from {path}; retry scan")
                return rows
            if expected is not None and len(rows) == expected:
                return rows
            page += 1


def login(user):
    value = user.get("login") if isinstance(user, dict) else None
    if not isinstance(value, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9\-\[\]]*", value):
        raise QueueError("author_identity_unknown", "A GitHub user identity is unavailable; no classification is safe")
    return value.casefold()


def owners(api, org):
    authenticated = login(api.get("/user"))
    membership = api.get(f"/user/memberships/orgs/{org}")
    if membership.get("state") != "active" or membership.get("role") not in ("admin", "member"):
        raise QueueError("owner_visibility_unknown", "Active organization membership with Members read visibility is required")
    roster = {login(u) for u in api.pages(f"/orgs/{org}/members", role="admin", filter="all")}
    if not roster or (membership["role"] == "admin" and authenticated not in roster):
        raise QueueError("owner_visibility_unknown", "Full organization admin enumeration could not be verified")
    return roster


def policy(api, root, branch):
    branch = quote(branch, safe="")
    protection = api.get(f"{root}/branches/{branch}/protection")
    rules = api.pages(f"{root}/rules/branches/{branch}")
    required = protection.get("required_status_checks") or {}
    checks = required.get("checks", [])
    contexts = required.get("contexts", [])
    reasons = []
    if rules:
        reasons.append(reason("unsupported_rulesets"))
    if required.get("strict") is not False:
        reasons.append(reason("unsupported_strict_policy"))
    if (not isinstance(checks, list) or not checks or not isinstance(contexts, list)
            or any(not isinstance(c, dict) or not isinstance(c.get("context"), str)
                   or not c["context"] or c.get("app_id") != ACTIONS_APP for c in checks)
            or set(contexts) != {c["context"] for c in checks}
            or len(checks) != len({c["context"] for c in checks})):
        reasons.append(reason("unsupported_required_checks"))
    return {"fingerprint": fingerprint({"protection": protection, "active_rules": rules}),
            "strict": required.get("strict"), "required_checks": checks,
            "active_rules_count": len(rules), "reasons": reasons}


def pr_identity(p):
    # strict=false: a moving base tip alone does not invalidate successful head CI.
    return {"number": p["number"], "author": login(p["user"]), "head_sha": p["head"]["sha"],
            "head_repo_id": (p["head"].get("repo") or {}).get("id"),
            "base_ref": p["base"]["ref"], "base_repo_id": p["base"]["repo"]["id"],
            "state": p["state"], "draft": p.get("draft"), "mergeable": p.get("mergeable"),
            "merge_commit_sha": p.get("merge_commit_sha")}


def pr_reasons(p, repo_id):
    reasons = []
    if p.get("state") != "open":
        reasons.append(reason("not_open"))
    if p.get("draft") is not False:
        reasons.append(reason("draft"))
    if p.get("mergeable") is False or p.get("mergeable_state") == "dirty":
        reasons.append(reason("conflict"))
    elif p.get("mergeable") is not True:
        reasons.append(reason("mergeability_unknown"))
    if not sha(p.get("merge_commit_sha")):
        reasons.append(reason("merge_candidate_unknown"))
    if (not sha(p["head"].get("sha")) or p["base"]["repo"].get("id") != repo_id
            or not positive((p["head"].get("repo") or {}).get("id"))):
        reasons.append(reason("pr_identity_unknown"))
    return reasons


def ci_run_identity(run):
    return {key: run.get(key) for key in (
        "id", "workflow_id", "path", "event", "head_sha", "check_suite_id", "run_attempt",
        "status", "conclusion", "repository", "pull_requests")}


def ci(api, root, repo, repo_id, p, rules):
    """Require every protected context in the latest observed applicable execution.

    Jobs from the exact attempt are joined to head check runs via their fixed API
    check_run_url. No details_url, PR URL, contents or workflow code is fetched.
    """
    evidence = {"workflow_path": WORKFLOW, "check_attachment_sha": p["head"]["sha"], "checks": []}
    workflow = api.get(f"{root}/actions/workflows/ci-pr.yml")
    if workflow.get("path") != WORKFLOW or not positive(workflow.get("id")) or workflow.get("state") != "active":
        return evidence, [reason("ci_workflow_unavailable")]
    workflow_id = workflow["id"]
    runs_path = f"{root}/actions/workflows/{workflow_id}/runs"
    runs = api.pages(runs_path, "workflow_runs", head_sha=p["head"]["sha"], event="pull_request")
    if not runs:
        return evidence, [reason("ci_run_missing")]
    if any(not positive(r.get("id")) for r in runs):
        return evidence, [reason("ci_source_mismatch")]
    # IDs order workflow executions; do not use updated_at (old runs can be rerun).
    latest = max(runs, key=lambda r: r["id"])
    run_id = latest["id"]
    run = api.get(f"{root}/actions/runs/{run_id}")
    evidence.update(run_id=run_id, workflow_id=workflow_id, run_attempt=run.get("run_attempt"),
                    check_suite_id=run.get("check_suite_id"), status=run.get("status"), conclusion=run.get("conclusion"))
    associations = [a for a in run.get("pull_requests", []) if a.get("number") == p["number"]]
    associated = any(a.get("head", {}).get("sha") == p["head"]["sha"]
                     and (a.get("head", {}).get("repo") or {}).get("id") == p["head"]["repo"]["id"]
                     and a.get("base", {}).get("ref") == p["base"]["ref"]
                     and (a.get("base", {}).get("repo") or {}).get("id") == repo_id for a in associations)
    if (run.get("id") != run_id or run.get("workflow_id") != workflow_id or run.get("path") != WORKFLOW
            or run.get("event") != "pull_request" or run.get("head_sha") != p["head"]["sha"]
            or run.get("repository", {}).get("id") != repo_id
            or run.get("repository", {}).get("full_name", "").casefold() != repo.casefold()
            or not positive(run.get("check_suite_id")) or not positive(run.get("run_attempt")) or not associated):
        return evidence, [reason("ci_source_mismatch")]
    evidence["associated_base_sha"] = associations[0].get("base", {}).get("sha")
    if run.get("status") != "completed" or run.get("conclusion") != "success":
        return evidence, [reason("ci_run_not_successful")]
    # Reexecuting an older run must not be hidden by a newer green run. This
    # conservative ambiguity rule deliberately asks for a fresh full execution.
    if any(r["id"] != run_id and (r.get("run_attempt", 1) > 1 or r.get("status") != "completed") for r in runs):
        return evidence, [reason("ci_execution_ambiguous")]
    attempt = run["run_attempt"]
    jobs = api.pages(f"{root}/actions/runs/{run_id}/attempts/{attempt}/jobs", "jobs")
    checks = api.pages(f"{root}/commits/{p['head']['sha']}/check-runs", "check_runs", filter="all")
    by_id = {c["id"]: c for c in checks}
    reasons = []
    selected_checks = set()
    for required in rules["required_checks"]:
        context, app_id = required["context"], required["app_id"]
        matching = [j for j in jobs if j.get("name") == context]
        if not matching:
            reasons.append(reason("required_job_missing", context=context))
        for job in matching:
            if job.get("status") != "completed" or job.get("conclusion") != "success":
                reasons.append(reason("required_job_not_successful", context=context))
            if (job.get("run_id") != run_id or job.get("run_attempt") != attempt
                    or job.get("head_sha") != p["head"]["sha"]):
                reasons.append(reason("required_check_source_mismatch", context=context))
                continue
            url = job.get("check_run_url", "")
            match = re.fullmatch(re.escape(f"https://api.github.com{root}/check-runs/") + r"([0-9]+)", url)
            if not match:
                reasons.append(reason("required_check_source_mismatch", context=context))
                continue
            check = by_id.get(int(match[1]))
            if check is None:
                reasons.append(reason("required_check_missing", context=context))
                continue
            selected_checks.add(check["id"])
            evidence["checks"].append({"context": context, "app_id": check.get("app", {}).get("id"),
                                       "check_run_id": check["id"], "job_id": job["id"],
                                       "status": check.get("status"), "conclusion": check.get("conclusion")})
            if (check.get("name") != context or check.get("head_sha") != p["head"]["sha"]
                    or check.get("app", {}).get("id") != app_id
                    or check.get("app", {}).get("slug") != "github-actions"
                    or check.get("check_suite", {}).get("id") != run["check_suite_id"]):
                reasons.append(reason("required_check_source_mismatch", context=context))
            if check.get("status") != "completed" or check.get("conclusion") != "success":
                reasons.append(reason("required_check_not_successful", context=context))
    # Protection binds context/app, not workflow. A competing non-success cannot
    # be discarded just because the chosen attempt's jobs do not reference it.
    required_apps = {r["context"]: r["app_id"] for r in rules["required_checks"]}
    competing = {c["id"]: c for c in checks
                 if c["id"] not in selected_checks and c.get("head_sha") == p["head"]["sha"]
                 and c.get("name") in required_apps
                 and c.get("app", {}).get("id") == required_apps[c["name"]]
                 and (c.get("status") != "completed" or c.get("conclusion") != "success")}
    # Only an earlier attempt of the selected execution can prove that its
    # matching failed check was superseded. Attempts are ordered by GitHub and
    # necessarily finished before the selected rerun. A competing check from a
    # different execution remains ambiguous: run_number and timestamps do not
    # establish completion ordering across executions.
    histories = [(run, a) for a in range(1, attempt)]
    for previous, previous_attempt in histories:
        suite = previous["check_suite_id"]
        if not any(c.get("check_suite", {}).get("id") == suite for c in competing.values()):
            continue
        old_jobs = api.pages(f"{root}/actions/runs/{previous['id']}/attempts/{previous_attempt}/jobs", "jobs")
        for job in old_jobs:
            if (job.get("run_id") != previous["id"] or job.get("run_attempt") != previous_attempt
                    or job.get("head_sha") != p["head"]["sha"]):
                continue
            for check_id, check in list(competing.items()):
                if (check.get("check_suite", {}).get("id") == suite
                        and job.get("name") == check["name"]
                        and job.get("check_run_url") == f"https://api.github.com{root}/check-runs/{check_id}"):
                    del competing[check_id]
    for check in competing.values():
        reasons.append(reason("required_check_ambiguous", context=check["name"],
                              check_run_id=check["id"], check_suite_id=check.get("check_suite", {}).get("id")))
    # GitHub requires both a check and a same-name legacy status to pass. The
    # combined endpoint returns the latest status per context, not its history.
    statuses = api.pages(f"{root}/commits/{p['head']['sha']}/status", "statuses")
    for status in statuses:
        if status.get("context") in required_apps and status.get("state") != "success":
            reasons.append(reason("required_status_not_successful", context=status["context"],
                                  status_id=status.get("id"), state=status.get("state")))
    # Observe a rerun that started during check retrieval before returning green.
    fresh_run = api.get(f"{root}/actions/runs/{run_id}")
    if ci_run_identity(fresh_run) != ci_run_identity(run):
        reasons.append(reason("ci_changed"))
    return evidence, reasons


def empty_snapshot(repo, pr_number=None):
    return {"schema_version": SCHEMA, "status": "ok", "repo": repo,
            "snapshot": {"started_at": now(), "completed_at": None, "focused_pr": pr_number,
                         "atomic": False, "owner_visibility": "unverified", "issues_scanned": pr_number is None},
            "prs": {"ready": [], "waiting": []}, "issues": {"triage": []},
            "excluded_owners": {"prs": 0, "issues": 0}}


def scan(api, repo=DEFAULT_REPO, pr_number=None):
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repo):
        raise QueueError("invalid_repository", "Use an organization/repository name on github.com")
    if pr_number is not None and not positive(pr_number):
        raise QueueError("invalid_pr", "PR number must be a positive integer")
    result = empty_snapshot(repo, pr_number)
    org = repo.split("/")[0]
    root = f"/repos/{repo}"
    roster = owners(api, org)
    repository = api.get(root)
    if repository.get("owner", {}).get("type") != "Organization" or not positive(repository.get("id")):
        raise QueueError("owner_visibility_unknown", "An organization-owned repository is required")
    if repository.get("full_name", "").casefold() != repo.casefold():
        raise QueueError("repository_changed", "Repository identity differs from requested repository")
    repo_id = repository["id"]
    result["snapshot"]["repository_id"] = repo_id
    pulls = [api.get(f"{root}/pulls/{pr_number}")] if pr_number else api.pages(root + "/pulls", state="open", sort="created", direction="asc")
    policies, candidates = {}, []
    for stub in pulls:
        if login(stub["user"]) in roster:
            result["excluded_owners"]["prs"] += 1
            continue
        number = stub["number"]
        if not positive(number) or (pr_number and number != pr_number):
            raise QueueError("invalid_api_response", "Invalid PR number")
        p = stub if pr_number else api.get(f"{root}/pulls/{number}")
        if login(p["user"]) in roster:
            result["excluded_owners"]["prs"] += 1
            continue
        if p["number"] != number or login(p["user"]) != login(stub["user"]):
            raise QueueError("pr_identity_changed", "PR identity changed during observation")
        row = {"number": number, "url": f"https://github.com/{repo}/pull/{number}",
               "author": p["user"]["login"], "title": p.get("title", ""),
               "head_sha": p["head"]["sha"], "observed_merge_sha": p.get("merge_commit_sha"),
               "base_ref": p["base"]["ref"], "base_sha": p["base"].get("sha"),
               "observed_at": now(), "policy": None, "ci": None, "reasons": pr_reasons(p, repo_id)}
        if not row["reasons"]:
            branch = p["base"]["ref"]
            if branch not in policies:
                policies[branch] = policy(api, root, branch)
            row["policy"] = policies[branch]
            row["reasons"].extend(row["policy"]["reasons"])
            if not row["reasons"]:
                row["ci"], row["reasons"] = ci(api, root, repo, repo_id, p, row["policy"])
        if row["reasons"]:
            result["prs"]["waiting"].append(row)
        else:
            candidates.append((p, row))
    if pr_number is None:
        for issue in api.pages(root + "/issues", state="open", sort="created", direction="asc"):
            if "pull_request" in issue:
                continue
            if login(issue["user"]) in roster:
                result["excluded_owners"]["issues"] += 1
                continue
            number = issue["number"]
            if not positive(number):
                raise QueueError("invalid_api_response", "Invalid Issue number")
            if issue.get("state") == "open":
                result["issues"]["triage"].append({"number": number, "url": f"https://github.com/{repo}/issues/{number}",
                                                    "author": issue["user"]["login"], "title": issue.get("title", ""),
                                                    "reasons": [reason("needs_triage")]})
    # Re-observe policy, execution and candidate identity at the end of the scan.
    # There is intentionally no atomicity claim across GitHub API calls.
    fresh_policies = {branch: policy(api, root, branch) for branch in {p["base"]["ref"] for p, _ in candidates}}
    for p, row in candidates:
        if fresh_policies[p["base"]["ref"]] != row["policy"]:
            row["reasons"].append(reason("policy_changed"))
        else:
            fresh_ci, failures = ci(api, root, repo, repo_id, p, row["policy"])
            if failures or fresh_ci != row["ci"]:
                row["reasons"].append(reason("ci_changed"))
        fresh_pr = api.get(f"{root}/pulls/{p['number']}")
        if pr_identity(fresh_pr) != pr_identity(p) or pr_reasons(fresh_pr, repo_id):
            row["reasons"].append(reason("snapshot_changed"))
        row["base_sha"] = fresh_pr["base"].get("sha")
        row["validated_at"] = now()
        result["prs"]["waiting" if row["reasons"] else "ready"].append(row)
    if owners(api, org) != roster:
        raise QueueError("owner_snapshot_changed", "Organization ownership changed during scan; retry without classifying submissions")
    result["snapshot"]["owner_visibility"] = "active_membership_and_admin_enumeration_rechecked"
    result["snapshot"]["completed_at"] = now()
    for rows in (result["prs"]["ready"], result["prs"]["waiting"], result["issues"]["triage"]):
        rows.sort(key=lambda row: row["number"])
    return result


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise QueueError("invalid_arguments", message)


def main(argv=None):
    parser = Parser(description=__doc__)
    parser.add_argument("--repo", default=DEFAULT_REPO, help="GitHub organization/repo (ci-pr policy adapter only)")
    parser.add_argument("--pr", type=int, help="Fresh focused selection; skips Issue and other PR lists")
    repo, number = DEFAULT_REPO, None
    try:
        args = parser.parse_args(argv)
        repo, number = args.repo, args.pr
        result = scan(GitHub(), repo, number)
        code = 0
    except QueueError as exc:
        result = empty_snapshot(repo, number)
        result.update(status="error", error={"code": exc.code, "message": str(exc)})
        result["snapshot"]["completed_at"] = now()
        code = 2
    except (KeyError, TypeError, ValueError, AttributeError) as exc:
        result = empty_snapshot(repo, number)
        result.update(status="error", error={"code": "invalid_api_response", "message": "GitHub evidence shape was incomplete; retry or inspect API permissions"})
        result["snapshot"]["completed_at"] = now()
        code = 2
    json.dump(result, sys.stdout, ensure_ascii=True, sort_keys=True, indent=2)
    sys.stdout.write("\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
