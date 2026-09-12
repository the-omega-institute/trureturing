"""Select a named dev push and compose a release from its validated common bundle."""
import argparse
import datetime
import gzip
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

from ci import CLI, RUNNER, checkout, extract, oid, outputs, run


def api(repository, path):
    return json.loads(subprocess.run(["gh", "api", "repos/" + repository + "/" + path],
                                    check=True, capture_output=True, text=True).stdout)


def pages(repository, path, field=None):
    data = json.loads(subprocess.run(["gh", "api", "--paginate", "--slurp", "repos/" + repository + "/" + path],
                                    check=True, capture_output=True, text=True).stdout)
    return [item for page in data for item in (page[field] if field else page)]


def collect(repository, commit, workflow):
    runs = pages(repository, "actions/workflows/ci-push.yml/runs?event=push&head_sha=" + commit + "&per_page=100", "workflow_runs")
    def artifacts(run):
        try:
            return pages(repository, f'actions/runs/{run["id"]}/artifacts?per_page=100', "artifacts")
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
            print("TRUTH_RELEASE_INPUT_UNAVAILABLE " + json.dumps({"run_id": run["id"], "reason": str(error)}))
            return []
    return {"source_commit": commit, "workflow": workflow, "runs": runs,
            "jobs": {str(row["id"]) + "/" + str(row["run_attempt"]):
                     pages(repository, f'actions/runs/{row["id"]}/attempts/{row["run_attempt"]}/jobs?per_page=100', "jobs")
                     for row in runs},
            "artifacts": {str(row["id"]): artifacts(row) for row in runs}}


def select(root, area, evidence):
    path = area / "push-evidence.json"
    path.write_text(json.dumps(evidence, sort_keys=True) + "\n")
    return json.loads(run(root, "dotnet", RUNNER, "truth-release-select", "--input", str(path)))


def restore_candidate(root, area, selected):
    commit = oid(selected["source_commit"])
    target = area / ("candidate-" + str(selected["run_id"]) + "-" + str(selected["run_attempt"]))
    if target.exists():
        shutil.rmtree(target)
    run(root, "git", "clone", "--quiet", "--no-hardlinks", "--no-checkout", str(root), str(target))
    run(target, "git", "checkout", "--quiet", "--detach", commit)
    checkout(target, commit)
    with tempfile.TemporaryDirectory(prefix="push-artifact-", dir=area) as temporary:
        archive = pathlib.Path(temporary) / "artifact.zip"
        with archive.open("wb") as stream:
            subprocess.run(["gh", "api", f'repos/{os.environ["GITHUB_REPOSITORY"]}/actions/artifacts/{selected["artifact_id"]}/zip'],
                           check=True, stdout=stream)
        with zipfile.ZipFile(archive) as transfer:
            if transfer.namelist() != ["ci-current.tar.gz"]:
                raise ValueError("selected push artifact has unexpected contents")
            transfer.extract("ci-current.tar.gz", temporary)
        extract(target, pathlib.Path(temporary) / "ci-current.tar.gz", "current")
    subprocess.run(["dotnet", RUNNER, "transport-verify", "--repository", str(target), "--stage", "current", "--commit", commit,
                    "--run-id", str(selected["run_id"]), "--run-attempt", str(selected["run_attempt"])], cwd=target, check=True)
    return target


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def assemble(root, area, selected):
    commit = oid(selected["source_commit"])
    tree = oid(run(root, "git", "rev-parse", "HEAD^{tree}"))
    epoch = int(run(root, "git", "show", "-s", "--format=%ct", "HEAD"))
    produced_at = datetime.datetime.fromtimestamp(epoch, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    bundle = area / "truth-release-bundle"
    assets = area / "truth-release-assets"
    for path in (bundle, assets):
        if path.exists(): shutil.rmtree(path)
        path.mkdir(parents=True)
    command = ["dotnet", CLI, "truth-release", "--out", str(bundle),
               "--candidate-lean-report", str(root / ".lake/build/stratalint/raw-lean-report.json"),
               "--producer-package-commit", commit, "--produced-at", produced_at, "--commit-on-protected-dev", "true"]
    for check in selected["required_checks"]:
        command.extend(["--required-check", check["name"] + "=" + check["conclusion"]])
    subprocess.run(command, cwd=root, check=True)
    manifest = json.loads((bundle / "release-manifest.v1.json").read_text())
    digest = manifest["sha256sums_digest"]
    if len(digest) != 71 or not digest.startswith("sha256:") or any(c not in "0123456789abcdef" for c in digest[7:]):
        raise ValueError("invalid release digest")
    publication_name = "truth-release-publication.v1.json"
    publication = json.loads((bundle / publication_name).read_text())
    if (publication["schema"] != "truth-release-publication.v1" or publication["release_digest"] != digest
            or publication["bundle_ref"] != digest or publication["source_commit"] != commit or publication["source_tree"] != tree):
        raise ValueError("release publication binding mismatch")
    oid(publication["producer_commit"])
    archive = assets / ("truth-release-" + digest[7:] + ".tar.gz")
    def normalize(member):
        member.uid = member.gid = member.mtime = 0
        member.uname = member.gname = ""
        return member
    with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w") as tar:
            for path in sorted(bundle.iterdir()):
                tar.add(path, arcname="./" + path.name, filter=normalize)
    shutil.copy2(bundle / publication_name, assets / publication_name)
    def material(path):
        return {"name": path.name, "sha256": sha(path), "size": path.stat().st_size}
    transfer = {"schema": "truth-release-transfer.v1", "repository": os.environ["GITHUB_REPOSITORY"],
                "run_id": os.environ["GITHUB_RUN_ID"], "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
                "source_commit": commit, "source_tree": tree, "release_digest": digest,
                "archive": material(archive), "publication": material(assets / publication_name)}
    (assets / "truth-release-transfer.v1.json").write_text(json.dumps(transfer, sort_keys=True) + "\n")
    print("TRUTH_RELEASE_INPUT " + json.dumps(selected, sort_keys=True))
    return {"artifact_name": "truth-release-publication-" + transfer["run_id"] + "-" + transfer["run_attempt"] + "-" + digest[7:],
            "release_digest": digest, "run_attempt": transfer["run_attempt"], "source_commit": commit, "source_tree": tree}


def prepare(root, area, repository):
    area.mkdir(parents=True, exist_ok=True)
    if api(repository, "branches/dev").get("protected") is not True:
        raise ValueError("dev is not protected")
    workflow = api(repository, "actions/workflows/ci-push.yml")
    # Preserve the existing newest-first, recent-40 protected-dev history policy.
    for row in api(repository, "commits?sha=dev&per_page=40"):
        commit = oid(row["sha"])
        evidence = collect(repository, commit, workflow)
        while (selected := select(root, area, evidence))["publish_ready"]:
            try:
                candidate = restore_candidate(root, area, selected)
            except (OSError, ValueError, subprocess.SubprocessError, tarfile.TarError, zipfile.BadZipFile) as error:
                print("TRUTH_RELEASE_INPUT_UNAVAILABLE " + json.dumps({"run_id": selected["run_id"], "reason": str(error)}))
                evidence["runs"] = [run for run in evidence["runs"] if run["id"] != selected["run_id"]]
                continue
            result = assemble(candidate, area, selected)
            outputs({**result, "publish_ready": True})
            return
    outputs({"publish_ready": False})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("prepare",))
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()
    try:
        prepare(args.repository.resolve(), args.output.resolve(), os.environ["GITHUB_REPOSITORY"])
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print("TRUTH_RELEASE_FAILED " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
