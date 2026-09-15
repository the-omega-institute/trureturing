"""Validate/bind report bundles and publish private, partitioned incremental seeds."""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import zipfile

from delta import parse_json_modules, valid_bundle, validate_materials, validate_report_sha

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts/worktree"))
from lean_cache import partition_path

SUFFIXES = ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json")


def member(report: pathlib.Path, suffix: str) -> pathlib.Path:
    return pathlib.Path(str(report) + suffix)


def seed_identity(report: pathlib.Path) -> str:
    return hashlib.sha256(member(report, ".seed.json").read_bytes()
        + member(report, ".provenance.json").read_bytes()).hexdigest()


def sha(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def validate(report: pathlib.Path) -> str:
    _, report_sha = parse_json_modules(report)
    validate_materials(report)
    return report_sha


def seed_valid(report: pathlib.Path, partition: str) -> bool:
    return valid_bundle(report, partition, allow_logs=True) is not None


def copy_bundle(report: pathlib.Path, output: pathlib.Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    for suffix in SUFFIXES:
        shutil.copyfile(member(report, suffix), member(output, suffix))
    member(output, ".sha256").write_text(f"{sha(output)}  {output.name}\n")


def bundle_hashes(report: pathlib.Path) -> dict[str, str]:
    return {suffix: sha(member(report, suffix)) for suffix in SUFFIXES}


def same_bundle(report: pathlib.Path, accepted: dict[str, str]) -> bool:
    try:
        return bundle_hashes(report) == accepted
    except OSError:
        return False


def stage(args: argparse.Namespace) -> None:
    # Transport carries the producer's seed identity; logs remain with its output.
    if valid_bundle(args.report, allow_logs=True) is None:
        raise ValueError("produced report bundle is invalid")
    copy_bundle(args.report, args.output)


def bind(args: argparse.Namespace) -> None:
    report_sha = validate(args.report)
    logs = member(args.report, ".logs")
    if not logs.is_dir() or not any(path.is_file() for path in logs.rglob("*")):
        raise ValueError("producer left no log sidecar")
    provenance = {"schema": "stratalint-lean-report-provenance-v1", "side": "candidate",
        "mode": "produced", "source_side": "candidate", "input_address": "sha256:" + args.input_address,
        "producer_sha256": args.producer_sha, "repository_inspector_sha256": args.producer_sha,
        "lean_sources_sha256": args.sources_sha, "lean_config_sha256": args.config_sha,
        "report_sha256": report_sha}
    member(args.report, ".provenance.json").write_text(json.dumps(provenance, separators=(",", ":")) + "\n")
    member(args.report, ".input.attestation").write_text(
        "schema=stratalint-lean-report-input-attestation-v1\n"
        + f"repository_input_sha256={args.repository_sha}\nproducer_sha256={args.producer_sha}\n"
        + f"report_sha256={report_sha}\n")
    # Runtime identity is produced by the executing inspector, never by a consumer.
    seed_path = member(args.report, ".seed.json")
    runtime = json.loads(seed_path.read_text()).get("runtime_sha256", "") if seed_path.is_file() else ""
    seed_path.write_text(json.dumps({"schema": "lean-report-seed-v1",
        "partition": partition_path(args.repository), "runtime_sha256": runtime,
        "report_sha256": report_sha, "materials_sha256": sha(member(args.report, ".materials.zip"))}, sort_keys=True) + "\n")


def store(args: argparse.Namespace, accepted: dict[str, str] | None = None) -> bool:
    partition = partition_path(args.repository) if args.repository else json.loads(
        member(args.report, ".seed.json").read_text(encoding="utf-8"))["partition"]
    import re
    if not isinstance(partition, str) or not re.fullmatch(r"[0-9a-f]{40}/(?:darwin|linux|windows)-[a-z0-9_]+", partition):
        raise ValueError("invalid report seed partition")
    # Only the combined publication/complete path supplies these in-memory bytes.
    # Ordinary store/import always validate an external seed in full.
    if accepted is None:
        usable = seed_valid(args.report, partition)
    else:
        usable = (same_bundle(args.report, accepted)
            and json.loads(member(args.report, ".seed.json").read_text())["partition"] == partition)
    if not usable:
        print("LEAN_REPORT_CACHE status=miss reason=unusable-bundle", file=sys.stderr)
        return False
    digests = bundle_hashes(args.report) if accepted is None else dict(accepted)
    digests[".sha256"] = hashlib.sha256(
        f"{digests['']}  raw-lean-report.json\n".encode("ascii")).hexdigest()
    cache = args.cache_root
    cache.mkdir(parents=True, exist_ok=True, mode=0o700)
    info = cache.stat()
    if cache.is_symlink() or info.st_uid != os.getuid() or info.st_mode & 0o022:
        raise ValueError("report cache root is not private")
    target = cache / partition
    target.mkdir(parents=True, exist_ok=True)
    identity = seed_identity(args.report)
    snapshot = target / identity
    if snapshot.is_dir():
        cached = snapshot / "raw-lean-report.json"
        if same_bundle(cached, digests):
            return True
        if seed_valid(cached, partition):
            return True
    if snapshot.exists():
        shutil.rmtree(snapshot)
    staged = pathlib.Path(tempfile.mkdtemp(prefix=".staging-", dir=target))
    try:
        report = staged / "raw-lean-report.json"
        copy_bundle(args.report, report)
        if not same_bundle(report, digests):
            raise ValueError("copied report differs from accepted source")
        try:
            staged.rename(snapshot)
        except OSError as error:
            if error.errno not in (errno.EEXIST, errno.ENOTEMPTY) and not isinstance(error, FileExistsError):
                raise
            winner = snapshot / "raw-lean-report.json"
            if not same_bundle(winner, digests) and not seed_valid(winner, partition):
                raise
        print(f"LEAN_REPORT_CACHE status=stored partition={partition} snapshot={snapshot.name}", file=sys.stderr)
    finally:
        shutil.rmtree(staged, ignore_errors=True)
    return True


def publish(args: argparse.Namespace) -> dict[str, str]:
    if not all(member(args.report, suffix).is_file() for suffix in SUFFIXES):
        raise ValueError("produced report bundle is invalid")
    # copy_bundle rebinds the checksum filename; validate the source sidecar
    # before copying, then validate all report/material content once in staging.
    validate_report_sha(args.report, sha(args.report))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # Production stays outside .lake until cold provisioning is finished. The
    # output can be on another filesystem (for example RUNNER_TEMP), so only
    # destination-local staging may participate in the final moves.
    with tempfile.TemporaryDirectory(prefix=".lean-report-publish-", dir=args.output.parent) as temporary:
        staged = pathlib.Path(temporary) / args.output.name
        copy_bundle(args.report, staged)
        staged_logs = member(staged, ".logs")
        shutil.copytree(member(args.report, ".logs"), staged_logs)
        accepted = bundle_hashes(staged)
        if (valid_bundle(staged, allow_logs=True) is None
                or not same_bundle(staged, accepted)
                or not any(path.is_file() for path in staged_logs.rglob("*"))):
            raise ValueError("staged report bundle is invalid")
        for suffix in SUFFIXES:
            os.replace(member(staged, suffix), member(args.output, suffix))
        logs = member(args.output, ".logs")
        if logs.is_dir():
            shutil.rmtree(logs)
        elif logs.exists():
            logs.unlink()
        staged_logs.rename(logs)
    return accepted


def publish_complete(args: argparse.Namespace) -> None:
    if (bool(args.preparation) != bool(args.execution)
            or args.cache_root and not args.preparation
            or args.preparation and not args.repository):
        raise ValueError("accepted publication requires repository, preparation and execution")
    accepted = publish(args)
    if args.preparation:
        from preparation import complete
        complete(args.repository, args.preparation, args.output, args.execution)
        if args.cache_root:
            try:
                store(argparse.Namespace(repository=args.repository, report=args.output,
                    cache_root=args.cache_root), accepted=accepted)
            except (OSError, ValueError, KeyError, TypeError, AttributeError, zipfile.BadZipFile) as error:
                print(f"LEAN_REPORT_CACHE status=miss reason=save-failed detail={error}", file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["bind", "stage", "store", "import", "publish", "validate"])
    parser.add_argument("--repository", type=pathlib.Path)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--cache-root", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--preparation", type=pathlib.Path)
    parser.add_argument("--execution", type=pathlib.Path)
    for field in ("input-address", "repository-sha", "producer-sha", "sources-sha", "config-sha"):
        parser.add_argument("--" + field)
    args = parser.parse_args()
    try:
        if args.command == "import":
            if store(args):
                print("LEAN_REPORT_CI_BASELINE status=ready", file=sys.stderr)
                print(args.cache_root)
            else:
                print("LEAN_REPORT_CI_BASELINE status=fallback reason=unusable-bundle", file=sys.stderr)
        elif args.command == "publish":
            publish_complete(args)
        elif args.command == "validate":
            validate(args.report)
        else:
            globals()[args.command](args)
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError, zipfile.BadZipFile,
            subprocess.CalledProcessError) as error:
        if args.command == "import":
            print(f"LEAN_REPORT_CI_BASELINE status=fallback reason={error}", file=sys.stderr)
            return 0
        print(f"lean-report-cache: {error}", file=sys.stderr)
        return 1 if args.command == "store" else 2


if __name__ == "__main__":
    raise SystemExit(main())
