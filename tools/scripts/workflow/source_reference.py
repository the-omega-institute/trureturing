"""Validate an explicit publication source against one protected branch snapshot."""
import re
import subprocess
from urllib.parse import quote


def validate_source_ref(repo, source_ref, source_commit, api):
    def commit(value):
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value) or value == "0" * 40:
            raise ValueError("source commit must be a nonzero immutable 40-hex SHA")
        return value

    commit(source_commit)
    if (not isinstance(source_ref, str) or not source_ref.startswith("refs/heads/")
            or subprocess.run(["git", "check-ref-format", source_ref], capture_output=True).returncode != 0):
        raise ValueError("source ref must be a full branch ref")
    branch = source_ref.removeprefix("refs/heads/")
    prefix = "repos/" + repo + "/"
    source = api(prefix + "branches/" + quote(branch, safe=""))
    if not isinstance(source, dict) or source.get("name") != branch or source.get("protected") is not True:
        raise ValueError("source branch is not protected or its identity differs")
    if not isinstance(source.get("commit"), dict):
        raise ValueError("source branch snapshot is missing its commit")
    tip = commit(source["commit"].get("sha"))
    comparison = api(prefix + "compare/" + source_commit + "..." + tip)
    if (not isinstance(comparison, dict) or comparison.get("status") not in ("ahead", "identical")
            or not isinstance(comparison.get("merge_base_commit"), dict)
            or comparison["merge_base_commit"].get("sha") != source_commit):
        raise ValueError("source commit is not on the protected branch snapshot")
    return branch
