"""Build and validate content-addressed Actions cache shards."""

from __future__ import annotations

import argparse
from collections import defaultdict
import fnmatch
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import tempfile

from lean_actions import (
    actions_keys, dependency_inputs, manual_source_is_valid, native_archive_paths, project_publication,
    receipt, resume_spec, write_small_record,
)
from lean_artifact_inventory import (
    PROJECT_BUILD, build_inventory, import_closure, lake_configuration, project_imports,
    required_compiler_paths, workspace_modules,
)
from lean_cache_release import cache_guard, install_scoped, report_reuse
from lean_cache_release_io import archive_sha, copy_chunks
from lean_cache_shards import group_identity, make_layout
from lean_release_index import safe_path, valid_digest

STAGE = Path("build/lean-cache/shards")
SCHEMA = "lean-actions-shards-v1"
EXTRAS = "extras"
REPORT = "report"
REPORT_PATH = "stratalint/raw-lean-report.json"
REPORT_RECEIPT = PurePosixPath(REPORT_PATH + ".reuse.json")
RESUME_RECORD = STAGE / "resumed.json"


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def binding(root, state):
    backend = actions_keys(root)
    key = {
        "schema": SCHEMA,
        "mathlib": backend["mathlib_revision"],
        "os": backend["os"],
        "arch": backend["arch"],
        "config": lake_configuration(root),
        "execution": dependency_inputs(root),
    }
    if state == "resume":
        key["producer_resume"] = resume_spec(root)["identity"]
        key["source_commit"] = source_commit(root)
    return key


def index_prefix(identity):
    return "lean-shard-index-v1-" + digest(identity) + "-"


def source_commit(root):
    return subprocess.check_output(["git", "rev-parse", "--verify", "HEAD"], cwd=root, text=True).strip()


def current_owner(root):
    return {"commit": source_commit(root), "ref": os.environ.get("GITHUB_REF", ""),
            "run": os.environ["GITHUB_RUN_ID"], "attempt": os.environ["GITHUB_RUN_ATTEMPT"]}


def transport_payload(path):
    return str(STAGE / "payload" / (path + ".tar.gz"))


def _tracked(relative, registrations):
    text = (PROJECT_BUILD / relative).as_posix()
    for spec in registrations:
        if "*" not in spec:
            if text == spec or text.startswith(spec + "/"):
                return True
        elif fnmatch.fnmatchcase(text, spec) or fnmatch.fnmatchcase(text, spec.replace("/**/", "/")):
            return True
    return False


def read_index(path, identity, state):
    if not path.is_file():
        return None

    def pairs(items):
        result = {}
        for name, value in items:
            if name in result:
                raise ValueError("duplicate Actions shard index field")
            result[name] = value
        return result

    with path.open("rb") as stream:
        data = stream.read(32 * 1024 * 1024 + 1)
    if len(data) > 32 * 1024 * 1024:
        raise ValueError("Actions shard index too large")
    record = json.loads(data, object_pairs_hook=pairs)
    if (not isinstance(record, dict) or record.get("binding") != identity or record.get("state") != state
            or set(record) != {"binding", "state", "owner", "layout", "entries", "sources", "fingerprints", "required"}):
        raise ValueError("incompatible Actions shard index")
    owner = record["owner"]
    if (not isinstance(owner, dict) or set(owner) != {"commit", "ref", "run", "attempt"}
            or not isinstance(owner["commit"], str) or not re.fullmatch(r"[0-9a-f]{40}", owner["commit"])
            or not isinstance(owner["ref"], str) or not re.fullmatch(r"refs/heads/(?:dev|integration-[A-Za-z0-9._/-]+)", owner["ref"])
            or not all(isinstance(owner[k], str) and re.fullmatch(r"[1-9][0-9]*", owner[k]) for k in ("run", "attempt"))):
        raise ValueError("invalid Actions shard owner")
    layout, entries, sources = record["layout"], record["entries"], record["sources"]
    if not all(isinstance(value, dict) for value in (layout, entries, sources)):
        raise ValueError("invalid Actions shard layout")
    used = set()
    for key, group in layout.items():
        if (not isinstance(group, list) or not 1 <= len(group) <= 8
                or not all(isinstance(shard, list) and 1 <= len(shard) <= 4 for shard in group)
                or digest(group) != key):
            raise ValueError("invalid Actions shard ID")
        for shard in group:
            for name in shard:
                if not isinstance(name, str) or not name or name in used:
                    raise ValueError("invalid or duplicate Actions shard module")
                used.add(name)
    if set(entries) - (set(layout) | {EXTRAS, REPORT}) or any(not valid_digest(value) for value in entries.values()):
        raise ValueError("invalid Actions shard entry")
    fingerprints = record["fingerprints"]
    if (not isinstance(fingerprints, dict) or set(fingerprints) != set(entries)
            or any(not valid_digest(value) for value in fingerprints.values())):
        raise ValueError("invalid Actions shard fingerprint")
    required = record["required"]
    if not isinstance(required, dict) or any(
            key not in entries or not isinstance(paths, list) or not paths
            or any(not isinstance(path, str) or str(safe_path(path)) != path for path in paths)
            or len(set(paths)) != len(paths)
            for key, paths in required.items()):
        raise ValueError("invalid required Actions shard inventory")
    if state == "resume" and required:
        raise ValueError("incomplete Actions shard index claims required output coverage")
    if state == "complete" and (REPORT not in required or required.keys() <= {REPORT, EXTRAS}):
        raise ValueError("complete Actions shard index lacks required outputs")
    if set(sources) != used or any(not valid_digest(value) for value in sources.values()):
        raise ValueError("invalid Actions source membership")
    return record


def tracked_sources(root, modules):
    return {name: archive_sha(root / module.source, None) for name, module in modules.items()}


def retained_layout(root, anchor, modules, graph, previous):
    if previous is None:
        return {group_identity(group): group for group in make_layout(root, anchor, modules, graph)}
    layout = {}
    owned = set()
    for group in previous["layout"].values():
        retained = tuple(tuple(name for name in shard if name in modules) for shard in group)
        retained = tuple(shard for shard in retained if shard)
        if retained:
            layout[group_identity(retained)] = retained
            owned.update(name for shard in retained for name in shard)
    for name in sorted(modules.keys() - owned):
        group = ((name,),)
        layout[group_identity(group)] = group
    return layout


def write_payload(root, build, paths):
    payload_dir = root / STAGE / "payload"
    payload_dir.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix="shard-", dir=payload_dir)
    candidate = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as destination:
            with gzip.GzipFile(filename="", fileobj=destination, mode="wb", compresslevel=1, mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w|") as archive:
                    for name in sorted(paths):
                        path = build / name
                        member = archive.gettarinfo(str(path), arcname=name)
                        if not member.isfile():
                            raise ValueError("Actions shard files must be regular")
                        member.uid = member.gid = member.mtime = 0
                        member.uname = member.gname = ""
                        member.mode &= 0o777
                        with path.open("rb") as source:
                            archive.addfile(member, source)
        payload = archive_sha(candidate, None)
        candidate.replace(root / transport_payload(payload))
        return payload
    finally:
        candidate.unlink(missing_ok=True)


def required_outputs(root, modules, graph, owners):
    selection = report_reuse.publication.selection.Selection(root)
    reported = selection.modules()
    if not reported or not reported.keys() <= modules.keys():
        raise ValueError("report modules do not match Actions workspace ownership")
    result = defaultdict(set)
    result[REPORT].update(REPORT_PATH + suffix for suffix in report_reuse.publication.SUFFIXES)
    result[REPORT].add(str(REPORT_RECEIPT))
    for name in import_closure(graph, reported):
        result[owners[name]].update(str(path) for path in required_compiler_paths(name, modules[name]))
    return {key: sorted(paths) for key, paths in result.items()}


def resume_verified(root):
    try:
        value = json.loads((root / RESUME_RECORD).read_text())
        return value == {"binding": binding(root, "resume"), "owner": current_owner(root)}
    except (OSError, ValueError, KeyError):
        return False


def prepare(root, identity, state, previous, anchor, targets=(), available=frozenset()):
    if state == "complete":
        allowed, reason, _ = project_publication(root)
        keys = actions_keys(root)
        migrated = reason == "no-build-work" and (manual_source_is_valid() or resume_verified(root))
        if (not (allowed or migrated) or not keys["project_save_allowed"]
                or os.environ.get("GITHUB_REF_PROTECTED") != "true"):
            raise ValueError("Actions shard publication denied: " + reason)
    else:
        resume_spec(root)
    with cache_guard(root, shared=True):
        if state == "complete":
            report = root / PROJECT_BUILD / REPORT_PATH
            report_reuse.read_receipt(report, report_reuse.capture(root))
        modules = workspace_modules(root)
        graph = project_imports(root, modules)
        inventory = build_inventory(root, modules)
        layout = retained_layout(root, anchor, modules, graph, previous)
        sources = tracked_sources(root, modules)
        registrations = native_archive_paths(root, ["project"])["project"]
        owners = {name: key for key, group in layout.items() for shard in group for name in shard}
        scoped_keys = {owners[name] for name in import_closure(graph, targets)} if targets else None
        groups = defaultdict(list)
        for artifact in inventory.artifacts:
            if _tracked(artifact.path, registrations):
                path = artifact.path.as_posix()
                if artifact.path.parent == REPORT_RECEIPT.parent and path.startswith(REPORT_PATH):
                    if state == "resume" and artifact.path == REPORT_RECEIPT:
                        continue
                    group = REPORT
                else:
                    group = owners.get(artifact.module, EXTRAS)
                if scoped_keys is None or group in scoped_keys:
                    groups[group].append(artifact.path.as_posix())

        required = required_outputs(root, modules, graph, owners) if state == "complete" else {}
        for key, paths in required.items():
            if not set(paths).issubset(groups.get(key, ())):
                absent = sorted(set(paths) - set(groups.get(key, ())))
                raise ValueError(f"project snapshot is missing compiler or report outputs: {absent[:5]}")
        build = root / PROJECT_BUILD
        fingerprints = {}
        entries = {}
        written = set()
        for key, paths in sorted(groups.items()):
            fingerprint = digest([(name, (build / name).stat().st_mode & 0o777, archive_sha(build / name, None))
                                  for name in sorted(paths)])
            fingerprints[key] = fingerprint
            retained = previous["entries"].get(key) if previous else None
            if retained in available and previous["fingerprints"][key] == fingerprint:
                entries[key] = retained
            else:
                entries[key] = write_payload(root, build, paths)
                written.add(entries[key])
    record = {"binding": identity, "owner": current_owner(root), "state": state, "layout": layout,
              "sources": sources, "entries": entries, "fingerprints": fingerprints}
    if state == "complete" and REPORT not in entries:
        raise ValueError("cannot publish a complete Actions index without the report bundle")
    receipt("shards", "snapshot", complete=state == "complete", entries=len(entries),
            packed=len(written), bytes=sum((root / transport_payload(item)).stat().st_size for item in written))
    return record


def selected_keys(root, record, targets):
    if not targets:
        return record["entries"]
    modules = workspace_modules(root)
    graph = project_imports(root, modules)
    names = import_closure(graph, targets)
    return {
        key: value for key, value in record["entries"].items()
        if key in (EXTRAS, REPORT) or any(names.intersection(shard) for shard in record["layout"][key])
    }


def extract_payload(path, destination, registrations, restored):
    with tarfile.open(path, "r|gz") as archive:
        for entry in archive:
            relative = safe_path(entry.name)
            if (not entry.isfile() or relative in restored or
                    not _tracked(relative, registrations)):
                raise ValueError("invalid archived Actions shard path: " + entry.name)
            target = destination / relative
            restored.add(relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(entry) as source, target.open("xb") as output:
                if copy_chunks(source, output, None) != entry.size:
                    raise ValueError("truncated Actions shard artifact: " + entry.name)
            target.chmod(entry.mode & 0o777)


def install(root, record, targets, *, require_complete=False):
    selected = selected_keys(root, record, targets)
    required = record["required"]
    registrations = native_archive_paths(root, ["project"])["project"]
    lake = root / ".lake"
    if lake.is_symlink():
        raise ValueError("Actions shards require a private build")
    lake.mkdir(exist_ok=True)
    available, missing = set(), set()
    with cache_guard(root), tempfile.TemporaryDirectory(prefix=".shards-", dir=lake) as temporary:
        unpacked = Path(temporary)
        paths = set()
        for key, digest_value in sorted(selected.items()):
            payload = root / transport_payload(digest_value)
            if not payload.is_file() or archive_sha(payload, None) != digest_value:
                missing.add(digest_value)
                continue
            entries = set()
            extract_payload(payload, unpacked, registrations, entries)
            if not set(required.get(key, ())).issubset(str(path) for path in entries):
                raise ValueError("Actions payload omits a required compiler or report output")
            if paths.intersection(entries):
                raise ValueError("duplicate artifact across Actions shards")
            paths.update(entries)
            available.add(digest_value)
        target = root / PROJECT_BUILD
        if target.is_symlink() or (target.is_dir() and any(target.iterdir())):
            raise ValueError("Actions shards require an empty build destination")
        if require_complete and missing:
            available.clear()
        else:
            install_scoped(target, unpacked, paths, None)
    complete = record["state"] == "complete" and not missing and not targets
    receipt("shards", "restore", complete=complete,
            restored=len(available), missing=len(missing), requested=len(selected))
    return {"available": len(available), "missing": sorted(missing), "requested": len(selected),
            "complete": complete}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("identity", "prepare", "restore-plan", "install"))
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--state", choices=("complete", "resume"), default="complete")
    parser.add_argument("--index", type=Path)
    parser.add_argument("--anchor")
    parser.add_argument("--available", type=Path)
    parser.add_argument("--target", action="append", default=[])
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    root = args.repository.resolve()
    identity = binding(root, args.state)
    if args.operation == "identity":
        print(json.dumps({"prefix": index_prefix(identity), "owner": current_owner(root)}))
        return
    record = read_index(args.index, identity, args.state) if args.index else None
    if args.operation == "prepare":
        if args.target and args.state != "resume":
            raise ValueError("scoped save requires an incomplete producer index")
        if record is None and (not args.anchor or not re.fullmatch(r"[0-9a-f]{40}", args.anchor)):
            raise ValueError("a fixed dev history anchor is required to seed the layout")
        available = set(json.loads(args.available.read_text())) if args.available else frozenset()
        print(json.dumps(prepare(root, identity, args.state, record, args.anchor, args.target, available),
                         separators=(",", ":")))
    elif record is None:
        raise ValueError("Actions shard index missing")
    elif args.operation == "restore-plan":
        print(json.dumps(selected_keys(root, record, args.target)))
    else:
        if args.state == "resume":
            (root / RESUME_RECORD).unlink(missing_ok=True)
        result = install(root, record, args.target, require_complete=args.require_complete)
        if args.state == "resume" and result["available"]:
            write_small_record(root / RESUME_RECORD, {"binding": identity, "owner": current_owner(root)})
        print(json.dumps(result))


if __name__ == "__main__":
    main()
