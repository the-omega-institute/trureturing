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

from materials import canonical_json, require_keys, require_sorted_strings, statement_address


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


def validate_report_sha(report: pathlib.Path, digest: str) -> None:
    lines = sidecar_path(report).read_text(encoding="ascii").splitlines()
    if len(lines) != 1:
        raise ValueError("report SHA sidecar is not one line")
    fields = lines[0].split(" ")
    if len(fields) != 3 or fields[1] != "" or fields[2] != report.name:
        raise ValueError("report SHA sidecar is malformed")
    if fields[0] != digest or not HEX64.fullmatch(fields[0]):
        raise ValueError("report SHA sidecar does not match report")


def parse_json_modules(report: pathlib.Path) -> tuple[dict[str, dict], str]:
    data = report.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    validate_report_sha(report, digest)
    root = json.loads(data.decode("utf-8"))
    require_keys(root, {"modules", "schema"}, "cached report")
    if root.get("schema") != "stratalint-raw-lean-report-v2" or not isinstance(root.get("modules"), list):
        raise ValueError("report schema is not canonical")
    modules: dict[str, dict] = {}
    for item in root["modules"]:
        if not isinstance(item, dict):
            raise ValueError("module record is not an object")
        module_keys = {"module", "source_path", "source_sha256", "imports", "declarations"}
        if "utility_refutation" in item:
            module_keys.add("utility_refutation")
        require_keys(item, module_keys, "cached module")
        name = item.get("module")
        source_path = item.get("source_path")
        source_sha = item.get("source_sha256")
        imports = item.get("imports")
        declarations = item.get("declarations")
        if (not isinstance(name, str) or not name or name in modules
                or modules and name <= next(reversed(modules))
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
            "refutation_claim_path": None,
        }
        require_sorted_strings(imports, "cached imports")
        previous = None
        for declaration in declarations:
            require_keys(declaration, {"axioms", "include_in_statement", "kind", "name", "name_key",
                "statement_id", "type_sha256"}, "cached declaration")
            key = declaration["name_key"]
            if (not all(isinstance(declaration[field], str) and declaration[field]
                        for field in ("kind", "name", "name_key"))
                    or not isinstance(declaration["include_in_statement"], bool)
                    or previous is not None and key <= previous):
                raise ValueError("cached declaration binding is malformed or unordered")
            require_sorted_strings(declaration["axioms"], "cached axioms")
            previous = key
        refutation = item.get("utility_refutation")
        if refutation is not None:
            require_keys(refutation, {"claim_gid", "claim_source_path", "claim_source_sha256",
                "result_gid", "is_closed_negation"}, "cached refutation")
            if (not all(isinstance(refutation[field], str) and refutation[field]
                        for field in ("claim_gid", "result_gid", "claim_source_path", "claim_source_sha256"))
                    or not SHA_FIELD.fullmatch(refutation["claim_source_sha256"])
                    or not isinstance(refutation["is_closed_negation"], bool)):
                raise ValueError("refutation source binding is malformed")
            modules[name]["refutation_claim_path"] = refutation["claim_source_path"]
    return modules, digest


def validate_materials(report: pathlib.Path) -> None:
    root = json.loads(report.read_text(encoding="utf-8"))
    with zipfile.ZipFile(materials_path(report)) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError("duplicate statement material")
        expected = set()
        for module in root["modules"]:
            for declaration in module["declarations"]:
                address = declaration["type_sha256"]
                name = "sha256/" + address[7:]
                material = archive.read(name)
                if statement_address(material) != address:
                    raise ValueError("statement material checksum mismatch")
                identity = statement_address(canonical_json({
                    "declaration_name_key": declaration["name_key"],
                    "kind": declaration["kind"], "module_path": module["source_path"],
                    "schema": "declaration-statement-v1",
                    "statement_material": material.decode("utf-8"),
                }))
                if identity != declaration["statement_id"]:
                    raise ValueError("declaration statement identity mismatch")
                expected.add(name)
        if set(names) != expected:
            raise ValueError("statement material archive does not match report")


def valid_bundle(report: pathlib.Path, partition: str = "", allow_logs: bool = False) -> tuple[dict[str, dict], str] | None:
    logs = pathlib.Path(str(report) + ".logs")
    if not allow_logs and (logs.exists() or logs.is_symlink()):
        return None
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
                or not re.fullmatch(r"producer_sha256=[0-9a-f]{64}", attestation_lines[2])
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
                or not SHA_FIELD.fullmatch(value.get("input_address", ""))
                or attestation_lines[2] != "producer_sha256=" + value.get("producer_sha256", "")
                or value.get("report_sha256") != report_sha):
            return None
        if any(not HEX64.fullmatch(value.get(field, "")) for field in (
                "producer_sha256", "repository_inspector_sha256", "lean_sources_sha256", "lean_config_sha256")):
            return None
        if partition:
            seed = json.loads(pathlib.Path(str(report) + ".seed.json").read_text(encoding="utf-8"))
            if (seed.get("schema") != "lean-report-seed-v1" or seed.get("partition") != partition
                    or seed.get("report_sha256") != report_sha
                    or seed.get("materials_sha256") != hashlib.sha256(materials_path(report).read_bytes()).hexdigest()
                    or not HEX64.fullmatch(seed.get("runtime_sha256", ""))):
                return None
        validate_materials(report)
        return modules, report_sha
    except (OSError, UnicodeError, ValueError, TypeError, AttributeError, KeyError, zipfile.BadZipFile):
        return None


def plan(args: argparse.Namespace) -> int:
    repository = pathlib.Path(args.repository)
    cache_root = pathlib.Path(args.cache_root)
    current = current_modules(pathlib.Path(args.module_table), repository)
    entries: list[tuple[int, pathlib.Path]] = []
    for entry in cache_root.iterdir() if cache_root.is_dir() else []:
        if not entry.is_dir():
            continue
        if not HEX64.fullmatch(entry.name):
            continue
        try:
            stamp = entry.stat().st_mtime_ns
        except OSError:
            continue
        entries.append((stamp, entry))
    # The caller supplies only this mathlib/platform partition. Semantic changes
    # invalidate module results below, never the compatibility of the seed.
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
                    or not SHA_FIELD.fullmatch(value.get("input_address", ""))):
                continue
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError):
            continue
        candidate = valid_bundle(entry / "raw-lean-report.json", args.partition)
        if candidate is not None:
            best = (stamp, entry, candidate[0], candidate[1])
            break

    if best is None:
        result: dict = {"status": "fallback"}
    else:
        _, entry, old, report_sha = best
        provenance = json.loads((entry / "raw-lean-report.json.provenance.json").read_text(encoding="utf-8"))
        semantic_changed = (provenance["producer_sha256"] != args.producer_sha
                            or provenance["repository_inspector_sha256"] != args.resident_sha
                            or provenance["lean_config_sha256"] != args.config_sha)
        if args.runtime_sha:
            try:
                seed = json.loads((entry / "raw-lean-report.json.seed.json").read_text(encoding="utf-8"))
                semantic_changed |= seed.get("runtime_sha256") != args.runtime_sha
            except (OSError, ValueError):
                semantic_changed = True
        changed = sorted(
            name for name in set(old) & set(current)
            if old[name]["path"] != current[name]["path"]
            or old[name]["source_sha256"] != current[name]["source_sha256"])
        added = sorted(set(current) - set(old))
        removed = sorted(set(old) - set(current))

        # The report edge points importer -> imported module.  For every
        # source-identical surviving importer, the attested old import list is
        # identical to the current one. Together with declared refutation inputs,
        # these edges close changed/added roots and surviving dependents of
        # removed modules without inspecting first.
        reverse = {name: set() for name in set(current) | set(old)}
        names_by_path = {record["path"]: name for name, record in old.items()}
        for importer, record in old.items():
            if importer not in current:
                continue
            for dependency in record.get("imports", []):
                if dependency in reverse:
                    reverse[dependency].add(importer)
            # A header-designated claim can affect definitional equality without a Lean import.
            claim_path = record.get("refutation_claim_path")
            if claim_path is not None:
                if claim_path not in names_by_path:
                    raise ValueError("refutation claim is absent from the baseline report")
                reverse[names_by_path[claim_path]].add(importer)

        # Deleted modules are not Inspector inputs, but their surviving importers
        # must be rechecked to avoid retaining records with unloadable environments.
        removed_importers = {
            importer
            for deleted in removed
            for importer in reverse.get(deleted, set())
            if importer in current
        }
        roots = set(changed) | set(added) | removed_importers
        if semantic_changed:
            roots = set(current)
        recheck = set(roots)
        pending = list(roots)
        while pending:
            module = pending.pop()
            for dependent in reverse.get(module, set()):
                if dependent in current and dependent not in recheck:
                    recheck.add(dependent)
                    pending.append(dependent)

        result = {
            "status": "reuse" if not changed and not added and not removed and not semantic_changed else "delta",
            "semantic_changed": semantic_changed,
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
                    if statement_address(material) != address:
                        raise ValueError(f"statement material checksum mismatch for {address}")
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
    planner.add_argument("--runtime-sha", default="")
    planner.add_argument("--partition", default="")
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
