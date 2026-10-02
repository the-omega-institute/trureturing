"""Read-only, perishable review eligibility for the protected required checks.

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


def mirrors_protection(rule, contexts):
    """True only for a non-strict Actions-bound required-checks rule restating `contexts` exactly."""
    parameters = rule.get("parameters") if rule.get("type") == "required_status_checks" else None
    if not isinstance(parameters, dict) or parameters.get("strict_required_status_checks_policy") is not False:
        return False
    required = parameters.get("required_status_checks")
    if not isinstance(required, list) or any(
            not isinstance(c, dict) or not isinstance(c.get("context"), str)
            or c.get("integration_id") != ACTIONS_APP for c in required):
        return False
    return sorted(c["context"] for c in required) == sorted(contexts)


def policy(api, root, branch):
    branch = quote(branch, safe="")
    protection = api.get(f"{root}/branches/{branch}/protection")
    rules = api.pages(f"{root}/rules/branches/{branch}")
    required = protection.get("required_status_checks") or {}
    checks = required.get("checks", [])
    contexts = required.get("contexts", [])
    reasons = []
    checks_unsupported = (not isinstance(checks, list) or not checks or not isinstance(contexts, list)
                          or any(not isinstance(c, dict) or not isinstance(c.get("context"), str)
                                 or not c["context"] or c.get("app_id") != ACTIONS_APP for c in checks)
                          or set(contexts) != {c["context"] for c in checks}
                          or len(checks) != len({c["context"] for c in checks}))
    # Rulesets are evaluated only when they restate the protected checks; anything else stays unmodelled.
    if rules and (checks_unsupported
                  or not all(mirrors_protection(r, [c["context"] for c in checks]) for r in rules)):
        reasons.append(reason("unsupported_rulesets"))
    if required.get("strict") is not False:
        reasons.append(reason("unsupported_strict_policy"))
    if checks_unsupported:
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


def ci(api, root, repo, repo_id, p, rules):
    """Aggregate the protected contexts at the fixed PR head, independently of workflow topology."""
    checks_path = f"{root}/commits/{p['head']['sha']}/check-runs"
    checks = api.pages(checks_path, "check_runs", filter="all")
    evidence = {"check_attachment_sha": p["head"]["sha"], "checks": []}
    reasons = []
    for required in rules["required_checks"]:
        context, app_id = required["context"], required["app_id"]
        matching = [c for c in checks if c.get("name") == context and c.get("app", {}).get("id") == app_id]
        if not matching:
            reasons.append(reason("required_check_missing", context=context))
            continue
        if any(not positive(c.get("id")) or c.get("head_sha") != p["head"]["sha"] for c in matching):
            reasons.append(reason("required_check_source_mismatch", context=context))
            continue
        check = max(matching, key=lambda c: c["id"])
        evidence["checks"].append({"context": context, "app_id": app_id, "check_run_id": check["id"],
                                   "status": check.get("status"), "conclusion": check.get("conclusion")})
        if check.get("status") != "completed" or check.get("conclusion") != "success":
            reasons.append(reason("required_check_not_successful", context=context))
    required_names = {r["context"] for r in rules["required_checks"]}
    statuses = api.pages(f"{root}/commits/{p['head']['sha']}/status", "statuses")
    for context in required_names:
        matching = [s for s in statuses if s.get("context") == context]
        if matching:
            latest = max(matching, key=lambda s: s.get("id", 0))
            if latest.get("state") != "success":
                reasons.append(reason("required_status_not_successful", context=context,
                                      status_id=latest.get("id"), state=latest.get("state")))
    fresh = api.pages(checks_path, "check_runs", filter="all")
    if fingerprint(fresh) != fingerprint(checks):
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
    parser.add_argument("--repo", default=DEFAULT_REPO, help="GitHub organization/repo (required-check policy adapter)")
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
