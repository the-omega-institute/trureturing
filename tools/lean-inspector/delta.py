#!/usr/bin/env python3
"""Plan and merge content-addressed module-level Lean report deltas.

This is deliberately a small, dependency-free helper.  It never changes the
report schema: merge() carries the original JSON object bytes for every module
that was not re-inspected and only replaces records produced by Inspector.lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import stat
import sys
import tempfile
import zipfile


HEX64 = re.compile(r"^[0-9a-f]{64}$")
SHA_FIELD = re.compile(r"^sha256:[0-9a-f]{64}$")
PREFIX = '{"modules": ['
SUFFIX = '], "schema": "stratalint-raw-lean-report-v2"}\n'
ARCHIVE_TIMESTAMP = (1980, 1, 1, 0, 0, 0)


def current_modules(module_table: pathlib.Path, repository: pathlib.Path) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for line in module_table.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        module, relative = line.split("\t", 1)
        path = repository / relative
        result[module] = {
            "path": relative,
            "source_sha256": "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest(),
        }
    return result


def sidecar_path(report: pathlib.Path) -> pathlib.Path:
    return pathlib.Path(str(report) + ".sha256")


def materials_path(report: pathlib.Path) -> pathlib.Path:
    return pathlib.Path(str(report) + ".materials.zip")


def parse_json_modules(report: pathlib.Path) -> tuple[dict[str, dict], str]:
    data = report.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    lines = sidecar_path(report).read_text(encoding="ascii").splitlines()
    if len(lines) != 1:
        raise ValueError("report SHA sidecar is not one line")
    fields = lines[0].split(" ")
    if len(fields) != 3 or fields[1] != "" or fields[2] != "raw-lean-report.json":
        raise ValueError("report SHA sidecar is malformed")
    if fields[0] != digest or not HEX64.fullmatch(fields[0]):
        raise ValueError("report SHA sidecar does not match report")
    root = json.loads(data.decode("utf-8"))
    if root.get("schema") != "stratalint-raw-lean-report-v2" or not isinstance(root.get("modules"), list):
        raise ValueError("report schema is not canonical")
    modules: dict[str, dict] = {}
    for item in root["modules"]:
        if not isinstance(item, dict):
            raise ValueError("module record is not an object")
        name = item.get("module")
        source_path = item.get("source_path")
        source_sha = item.get("source_sha256")
        imports = item.get("imports")
        declarations = item.get("declarations")
        if (not isinstance(name, str) or not name or name in modules
                or not isinstance(source_path, str) or not source_path
                or not isinstance(source_sha, str) or not SHA_FIELD.fullmatch(source_sha)
                or not isinstance(imports, list)
                or any(not isinstance(value, str) for value in imports)
                or not isinstance(declarations, list)
                or any(not isinstance(value, dict)
                       or not SHA_FIELD.fullmatch(value.get("type_sha256", ""))
                       or not SHA_FIELD.fullmatch(value.get("statement_id", ""))
                       for value in declarations)):
            raise ValueError("module record is malformed")
        modules[name] = {
            "path": source_path,
            "source_sha256": source_sha,
            "imports": imports,
        }
    return modules, digest


def valid_baseline(
    entry: pathlib.Path,
    current_address: str,
    producer_sha: str,
    resident_sha: str,
    config_sha: str,
) -> tuple[dict[str, dict], str] | None:
    if not HEX64.fullmatch(entry.name) or entry.name == current_address:
        return None
    report = entry / "raw-lean-report.json"
    attestation = pathlib.Path(str(report) + ".input.attestation")
    provenance = pathlib.Path(str(report) + ".provenance.json")
    if not (report.is_file() and sidecar_path(report).is_file()
            and materials_path(report).is_file()
            and attestation.is_file() and provenance.is_file()):
        return None
    try:
        modules, report_sha = parse_json_modules(report)
        attestation_lines = attestation.read_text(encoding="ascii").splitlines()
        if (len(attestation_lines) != 4
                or attestation_lines[0] != "schema=stratalint-lean-report-input-attestation-v1"
                or not re.fullmatch(r"repository_input_sha256=[0-9a-f]{64}", attestation_lines[1])
                or attestation_lines[2] != "producer_sha256=" + producer_sha
                or attestation_lines[3] != "report_sha256=" + report_sha):
            return None
        value = json.loads(provenance.read_text(encoding="utf-8"))
        if (set(value) != {
                    "schema", "side", "mode", "source_side", "input_address",
                    "producer_sha256", "repository_inspector_sha256",
                    "lean_sources_sha256", "lean_config_sha256", "report_sha256"}
                or value.get("schema") != "stratalint-lean-report-provenance-v1"
                or value.get("side") != "candidate"
                or value.get("source_side") != "candidate"
                or value.get("mode") not in ("produced", "cached")
                or value.get("input_address") != "sha256:" + entry.name
                or value.get("producer_sha256") != producer_sha
                or value.get("repository_inspector_sha256") != resident_sha
                or value.get("lean_config_sha256") != config_sha
                or value.get("report_sha256") != report_sha):
            return None
        return modules, report_sha
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError, KeyError):
        return None


def plan(args: argparse.Namespace) -> int:
    repository = pathlib.Path(args.repository)
    cache_root = pathlib.Path(args.cache_root)
    current = current_modules(pathlib.Path(args.module_table), repository)
    entries: list[tuple[int, pathlib.Path]] = []
    for entry in cache_root.iterdir():
        if not entry.is_dir():
            continue
        if not HEX64.fullmatch(entry.name) or entry.name == args.current_address:
            continue
        try:
            stamp = entry.stat().st_mtime_ns
        except OSError:
            continue
        entries.append((stamp, entry))
    # Provenance is tiny compared with a report (the production report is
    # hundreds of MB), so reject identity-mismatched entries before opening the
    # report.  Newest valid candidate wins; older entries are only inspected when
    # a newer entry is incomplete or malformed.
    entries.sort(reverse=True, key=lambda value: value[0])
    best: tuple[int, pathlib.Path, dict[str, dict], str] | None = None
    for stamp, entry in entries:
        provenance = entry / "raw-lean-report.json.provenance.json"
        try:
            value = json.loads(provenance.read_text(encoding="utf-8"))
            if (value.get("schema") != "stratalint-lean-report-provenance-v1"
                    or value.get("side") != "candidate"
                    or value.get("source_side") != "candidate"
                    or value.get("mode") not in ("produced", "cached")
                    or value.get("input_address") != "sha256:" + entry.name
                    or value.get("producer_sha256") != args.producer_sha
                    or value.get("repository_inspector_sha256") != args.resident_sha
                    or value.get("lean_config_sha256") != args.config_sha):
                continue
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError):
            continue
        candidate = valid_baseline(
            entry, args.current_address, args.producer_sha, args.resident_sha,
            args.config_sha)
        if candidate is not None:
            best = (stamp, entry, candidate[0], candidate[1])
            break

    if best is None:
        result: dict = {"status": "fallback"}
    else:
        _, entry, old, report_sha = best
        changed = sorted(
            name for name in set(old) & set(current)
            if old[name]["path"] != current[name]["path"]
            or old[name]["source_sha256"] != current[name]["source_sha256"])
        added = sorted(set(current) - set(old))
        removed = sorted(set(old) - set(current))

        # The report edge points importer -> imported module.  For every
        # source-identical surviving importer, the attested old import list is
        # identical to the current one.  It is therefore the complete inbound
        # graph needed to close changed/added roots without inspecting first.
        reverse = {name: set() for name in set(current) | set(old)}
        for importer, record in old.items():
            if importer not in current:
                continue
            for dependency in record.get("imports", []):
                if dependency in reverse:
                    reverse[dependency].add(importer)

        roots = set(changed) | set(added)
        recheck = set(roots)
        pending = list(roots)
        while pending:
            module = pending.pop()
            for dependent in reverse.get(module, set()):
                if dependent in current and dependent not in recheck:
                    recheck.add(dependent)
                    pending.append(dependent)

        # A deleted module is not an Inspector input, but an old importer still
        # naming it must be rechecked so deletion cannot silently preserve a
        # record whose environment is no longer loadable.
        for deleted in removed:
            for importer in reverse.get(deleted, set()):
                if importer in current:
                    recheck.add(importer)

        result = {
            "status": "reuse" if not changed and not added and not removed else "delta",
            "baseline": str(entry / "raw-lean-report.json"),
            "baseline_report_sha256": report_sha,
            "changed": changed,
            "added": added,
            "removed": removed,
            "recheck": sorted(recheck),
            "current": current,
        }
    pathlib.Path(args.plan).write_text(json.dumps(result, sort_keys=True), encoding="utf-8")
    return 0


def raw_modules(report: pathlib.Path) -> dict[str, tuple[str, dict]]:
    text = report.read_text(encoding="utf-8")
    if not text.startswith(PREFIX) or not text.endswith(SUFFIX):
        raise ValueError("non-canonical report framing")
    body = text[len(PREFIX):-len(SUFFIX)]
    decoder = json.JSONDecoder()
    position = 0
    result: dict[str, tuple[str, dict]] = {}
    while position < len(body):
        if body[position] in " ,":
            position += 1
            continue
        start = position
        value, position = decoder.raw_decode(body, position)
        if not isinstance(value, dict) or not isinstance(value.get("module"), str):
            raise ValueError("module record is malformed")
        name = value["module"]
        if name in result:
            raise ValueError("duplicate module record")
        result[name] = (body[start:position], value)
    return result


def merge(args: argparse.Namespace) -> int:
    plan_value = json.loads(pathlib.Path(args.plan).read_text(encoding="utf-8"))
    baseline = raw_modules(pathlib.Path(plan_value["baseline"]))
    subset_path = pathlib.Path(args.subset)
    subset = raw_modules(subset_path) if subset_path.is_file() and subset_path.stat().st_size else {}
    recheck = set(plan_value.get("recheck", []))
    if set(subset) != recheck:
        raise ValueError("subset report does not match recheck set")
    current = plan_value["current"]
    if set(baseline) - set(current) != set(plan_value.get("removed", [])):
        raise ValueError("baseline removal set changed during production")

    merged: dict[str, str] = {}
    merged_values: dict[str, dict] = {}
    for name in current:
        if name in recheck:
            raw, value = subset[name]
            expected = current[name]
            if (value.get("source_path") != expected["path"]
                    or value.get("source_sha256") != expected["source_sha256"]):
                raise ValueError("subset source binding does not match current tree")
            merged[name] = raw
            merged_values[name] = value
        else:
            if name not in baseline:
                raise ValueError("unchanged module is absent from baseline")
            raw, value = baseline[name]
            expected = current[name]
            if (value.get("source_path") != expected["path"]
                    or value.get("source_sha256") != expected["source_sha256"]):
                raise ValueError("unchanged module is not unchanged")
            merged[name] = raw
            merged_values[name] = value

    output = pathlib.Path(args.output)
    output_materials = materials_path(output)
    staged = pathlib.Path(tempfile.mkdtemp(prefix=".lean-delta-materials.", dir=output.parent))
    staged_archive = staged / "materials.zip"
    try:
        addresses = sorted({
            declaration["type_sha256"]
            for value in merged_values.values()
            for declaration in value["declarations"]
        })
        source_paths = (
            materials_path(subset_path),
            materials_path(pathlib.Path(plan_value["baseline"])),
        )
        sources = [
            zipfile.ZipFile(path, "r") if path.is_file() else None
            for path in source_paths
        ]
        try:
            with zipfile.ZipFile(
                    staged_archive, "w", compression=zipfile.ZIP_DEFLATED,
                    compresslevel=6, allowZip64=True) as destination:
                for address in addresses:
                    name = "sha256/" + address[7:]
                    material = None
                    for source in sources:
                        if source is None:
                            continue
                        try:
                            material = source.read(name)
                            break
                        except KeyError:
                            continue
                    if material is None:
                        raise ValueError(f"statement material is missing for {address}")
                    info = zipfile.ZipInfo(name, ARCHIVE_TIMESTAMP)
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.create_system = 3
                    info.external_attr = (stat.S_IFREG | 0o644) << 16
                    destination.writestr(info, material)
        finally:
            for source in sources:
                if source is not None:
                    source.close()
        if output_materials.exists():
            output_materials.unlink()
        staged_archive.replace(output_materials)
        output.write_text(
            PREFIX + ", ".join(merged[name] for name in sorted(current)) + SUFFIX,
            encoding="utf-8",
        )
    finally:
        shutil.rmtree(staged, ignore_errors=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    planner = subparsers.add_parser("plan")
    planner.add_argument("repository")
    planner.add_argument("cache_root")
    planner.add_argument("current_address")
    planner.add_argument("producer_sha")
    planner.add_argument("resident_sha")
    planner.add_argument("config_sha")
    planner.add_argument("module_table")
    planner.add_argument("plan")
    planner.set_defaults(function=plan)
    merger = subparsers.add_parser("merge")
    merger.add_argument("plan")
    merger.add_argument("subset")
    merger.add_argument("output")
    merger.set_defaults(function=merge)
    args = parser.parse_args()
    try:
        return args.function(args)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"lean-report-delta: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
