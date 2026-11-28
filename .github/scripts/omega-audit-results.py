"""Transfer fresh Omega audit records between verified GitHub Actions runs."""

import argparse
from functools import cache
import hashlib
import http.client
import io
import json
import os
from pathlib import Path
import re
import stat
import tempfile
from time import monotonic
import urllib.parse
import urllib.request
import zipfile
import zlib


NAME = "omega-audit-results-v1"
WORKFLOW = ".github/workflows/ci-current.yml"
PUBLISH_STEP = "Upload fresh Omega audit records"
RECORD = re.compile(r"[0-9a-f]{64}\.json")
MIB = 1024 * 1024
RECORD_BYTES = 32 * MIB
ARCHIVE_BYTES = 64 * MIB
RESTORE_BYTES = 128 * MIB
MAX_RECORDS = 2048
MAX_BATCHES = 12
CACHE_ERRORS = (OSError, ValueError, KeyError, TypeError, http.client.HTTPException,
                zipfile.BadZipFile, zlib.error, EOFError)


def producer(env):
    return {"repository_id": int(env["GITHUB_REPOSITORY_ID"]), "run_id": int(env["GITHUB_RUN_ID"]),
            "attempt": int(env["GITHUB_RUN_ATTEMPT"]), "sha": env["GITHUB_SHA"], "branch": env["GITHUB_REF_NAME"]}


def prepare(directory, env):
    """Only the protected push's freshly executed records are eligible for upload."""
    branch = env.get("GITHUB_REF_NAME", "")
    if (env.get("GITHUB_EVENT_NAME") != "push" or env.get("GITHUB_REF_PROTECTED") != "true"
            or env.get("GITHUB_REF_TYPE") != "branch" or not (branch == "dev" or branch.startswith("integration-"))):
        return None
    produced = directory / "produced"
    if not produced.is_dir():
        return None
    sources = []
    total = 0
    for path in produced.iterdir():
        info = path.lstat()
        if not (RECORD.fullmatch(path.name) and stat.S_ISREG(info.st_mode) and 0 < info.st_size <= RECORD_BYTES):
            raise ValueError("invalid produced Omega record")
        total += info.st_size
        sources.append(path)
        if total > RESTORE_BYTES or len(sources) > MAX_RECORDS:
            raise ValueError("produced Omega batch exceeds capacity")
    if not sources:
        return None
    stage = Path(tempfile.mkdtemp(prefix="upload-", dir=directory))
    for path in sources:
        os.link(path, stage / path.name)
    (stage / "producer.json").write_text(json.dumps(producer(env)), encoding="utf-8")
    return stage


class GitHub:
    def __init__(self, env):
        self.repo = env["GITHUB_REPOSITORY"]
        self.repo_id = int(env["GITHUB_REPOSITORY_ID"])
        self.api = env["GITHUB_API_URL"].rstrip("/") + "/repos/" + self.repo
        self.token = env["GH_TOKEN"]
        self.deadline = monotonic() + 90

    def read(self, path, limit):
        remaining = self.deadline - monotonic()
        if remaining <= 0:
            raise TimeoutError("Omega artifact lookup time expired")
        request = urllib.request.Request(self.api + "/" + path, headers={
            "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"})
        # GitHub redirects archive requests to signed blob URLs on a different host.
        request.add_unredirected_header("Authorization", "Bearer " + self.token)
        with urllib.request.urlopen(request, timeout=min(15, remaining)) as response:
            raw = response.read(limit + 1)
        if len(raw) > limit:
            raise ValueError("GitHub response exceeds capacity")
        return raw

    def metadata(self, path):
        return json.loads(self.read(path, 2 * MIB))

    @cache
    def protected_tip(self, branch):
        result = self.metadata("branches/" + urllib.parse.quote(branch, safe=""))
        if result["name"] == branch and result["protected"] is True:
            return result["commit"]["sha"]
        return None


def provenance(api, artifact):
    source = artifact["workflow_run"]
    branch, sha, run_id = source["head_branch"], source["head_sha"], source["id"]
    tip = api.protected_tip(branch)
    if tip is None:
        return None
    run = api.metadata(f"actions/runs/{run_id}")
    if (run["id"] != run_id or run["repository"]["id"] != api.repo_id or run["head_repository"]["id"] != api.repo_id
            or run["head_sha"] != sha or run["head_branch"] != branch or run["event"] != "push"
            or run["path"] != WORKFLOW or run["status"] != "completed" or run["conclusion"] != "success"):
        return None
    if tip != sha:
        # Page two omits the first page's potentially very large diff.
        comparison = api.metadata(f"compare/{sha}...{tip}?per_page=1&page=2")
        if comparison["status"] != "ahead":
            return None
    attempt = run["run_attempt"]
    jobs = api.metadata(f"actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100")["jobs"]
    for job in jobs:
        if (job["name"] == "omega-consumer" and job["run_id"] == run_id and job["run_attempt"] == attempt
                and job["head_sha"] == sha and job["status"] == "completed" and job["conclusion"] == "success"
                and any(step["name"] == PUBLISH_STEP and step["conclusion"] == "success" for step in job["steps"])):
            return {"repository_id": api.repo_id, "run_id": run_id, "attempt": attempt, "sha": sha, "branch": branch}
    return None


def unpack(raw, expected, byte_limit, record_limit):
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        entries = archive.infolist()
        if len(entries) > record_limit + 1 or sum(entry.file_size for entry in entries) > byte_limit + 1024:
            raise ValueError("audit batch exceeds restore capacity")
        rows = {}
        details = None
        for entry in entries:
            name = entry.orig_filename
            if (name != entry.filename or stat.S_IFMT(entry.external_attr >> 16) not in (0, stat.S_IFREG)
                    or entry.compress_type not in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED) or entry.flag_bits & 1):
                raise ValueError("invalid ZIP member")
            if name == "producer.json" and details is None and 0 < entry.file_size <= 1024:
                with archive.open(entry) as source:
                    details = source.read(entry.file_size + 1)
            elif RECORD.fullmatch(name) and name not in rows and 0 < entry.file_size <= RECORD_BYTES:
                with archive.open(entry) as source:
                    rows[name] = source.read(entry.file_size + 1)
            else:
                raise ValueError("invalid or duplicate Omega audit record")
        if not details or json.loads(details) != expected or sum(map(len, rows.values())) > byte_limit:
            raise ValueError("audit batch differs from its producer or exceeds restore capacity")
        return rows


def restore(api, base, directory):
    branches = {"dev"}
    if base.startswith("integration-"):
        branches.add(base)
    artifacts = api.metadata(f"actions/artifacts?name={NAME}&per_page=100")["artifacts"]
    conflicts = set()
    batches = transferred = staged = 0
    with tempfile.TemporaryDirectory(dir=directory) as temp:
        records = Path(temp) / "records"
        records.mkdir()
        digests = {}
        for artifact in artifacts:
            if batches == MAX_BATCHES:
                break
            try:
                source = artifact["workflow_run"]
                if (artifact["name"] != NAME or artifact["expired"] is not False
                        or source["head_branch"] not in branches or source["repository_id"] != api.repo_id
                        or source["head_repository_id"] != api.repo_id
                        or not re.fullmatch(r"[0-9a-f]{40}", source["head_sha"])
                        or not re.fullmatch(r"sha256:[0-9a-f]{64}", artifact["digest"])):
                    continue
                size = artifact["size_in_bytes"]
                if not 0 < size <= min(ARCHIVE_BYTES, RESTORE_BYTES - transferred):
                    continue
                batches += 1
                expected = provenance(api, artifact)
                if expected is None:
                    continue
                transferred += size
                raw = api.read(f"actions/artifacts/{int(artifact['id'])}/zip", size)
                if len(raw) != size or "sha256:" + hashlib.sha256(raw).hexdigest() != artifact["digest"]:
                    raise ValueError("Omega artifact ZIP differs from the GitHub digest or size")
                rows = unpack(raw, expected, RESTORE_BYTES - staged, MAX_RECORDS - len(digests))
            except CACHE_ERRORS as error:
                print(f"Skipped Omega artifact {artifact.get('id')}: {error}", flush=True)
                continue
            for name, data in rows.items():
                if name in conflicts:
                    continue
                path = records / name
                digest = hashlib.sha256(data).digest()
                if name not in digests:
                    path.write_bytes(data)
                    digests[name] = digest
                    staged += len(data)
                elif digests[name] != digest:
                    conflicts.add(name)
                    staged -= path.stat().st_size
                    path.unlink()
                    del digests[name]
        records.rename(directory / "restored")
    print(f"Omega audit restore: {len(digests)} records, {len(conflicts)} conflicting keys, {transferred} bytes")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("restore", "prepare-upload"))
    args = parser.parse_args()
    directory = Path(os.environ["OMEGA_AUDIT_CACHE"])
    if args.operation == "restore":
        base = os.environ.get("GITHUB_BASE_REF") or os.environ["GITHUB_REF_NAME"]
        restore(GitHub(os.environ), base, directory)
    elif upload := prepare(directory, os.environ):
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
            print(f"path={upload}", file=output)


if __name__ == "__main__":
    main()
