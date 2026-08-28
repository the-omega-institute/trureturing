#!/usr/bin/env python3
"""Compact Inspector statement spools into the canonical v2 report bundle."""

from __future__ import annotations

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


SPOOL_SCHEMA = "stratalint-lean-inspector-spool-v1"
REPORT_SCHEMA = "stratalint-raw-lean-report-v2"
STATEMENT_DOMAIN = b"trureturing:statement:v1\0"
MATERIAL_FILE = re.compile(r"^[0-9]+\.statement$")
SUPPLEMENTARY_SCALAR = re.compile(r"[\U00010000-\U0010FFFF]")
ARCHIVE_TIMESTAMP = (1980, 1, 1, 0, 0, 0)


def escape_supplementary_scalar(match: re.Match[str]) -> str:
    offset = ord(match.group()) - 0x10000
    return f"\\u{0xD800 + offset // 0x400:04X}\\u{0xDC00 + offset % 0x400:04X}"


def canonical_json(value: object) -> bytes:
    text = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(", ", ": "),
        allow_nan=False,
    )
    # System.Text.Json's UnsafeRelaxedJsonEscaping leaves ordinary Unicode
    # scalars intact but renders supplementary-plane scalars as uppercase UTF-16
    # surrogate pairs. StructuredCanonicalWriter therefore has this exact byte
    # shape, and declaration identity includes it.
    return (SUPPLEMENTARY_SCALAR.sub(escape_supplementary_scalar, text) + "\n").encode("utf-8")


def statement_address(material: bytes) -> str:
    return "sha256:" + hashlib.sha256(STATEMENT_DOMAIN + material).hexdigest()


def require_keys(value: object, expected: set[str], context: str) -> dict:
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError(f"{context} has unexpected fields")
    return value


def require_sorted_strings(value: object, context: str) -> list[str]:
    if (not isinstance(value, list)
            or any(not isinstance(item, str) for item in value)
            or value != sorted(set(value))):
        raise ValueError(f"{context} must be sorted and unique strings")
    return value


def regular_spool_file(spool: pathlib.Path, relative: str) -> pathlib.Path:
    if not MATERIAL_FILE.fullmatch(relative):
        raise ValueError("statement material spool name is malformed")
    path = spool / relative
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError as error:
        raise ValueError(f"statement material spool is missing: {relative}") from error
    if not stat.S_ISREG(mode):
        raise ValueError(f"statement material spool is not a regular file: {relative}")
    return path


def compact(spool_report: pathlib.Path, spool: pathlib.Path, output: pathlib.Path) -> None:
    root = json.loads(spool_report.read_text(encoding="utf-8"))
    require_keys(root, {"modules", "schema"}, "Inspector spool")
    if root["schema"] != SPOOL_SCHEMA or not isinstance(root["modules"], list):
        raise ValueError("Inspector spool schema is invalid")

    output.parent.mkdir(parents=True, exist_ok=True)
    staged_root = pathlib.Path(tempfile.mkdtemp(prefix=".lean-materials.", dir=output.parent))
    staged_materials = staged_root / "materials" / "sha256"
    staged_materials.mkdir(parents=True)
    referenced_spools: set[str] = set()
    modules: list[dict] = []
    previous_module: str | None = None
    declaration_count = 0
    material_bytes = 0
    try:
        for raw_module in root["modules"]:
            module = require_keys(
                raw_module,
                {"declarations", "imports", "module", "source_path", "source_sha256"},
                "Inspector spool module",
            )
            module_name = module["module"]
            source_path = module["source_path"]
            source_sha256 = module["source_sha256"]
            if (not isinstance(module_name, str) or not module_name
                    or previous_module is not None and module_name <= previous_module
                    or not isinstance(source_path, str) or not source_path
                    or not isinstance(source_sha256, str)):
                raise ValueError("Inspector spool module binding is malformed or unordered")
            previous_module = module_name
            imports = require_sorted_strings(module["imports"], "Inspector spool imports")
            if not isinstance(module["declarations"], list):
                raise ValueError("Inspector spool declarations must be an array")

            declarations: list[dict] = []
            previous_name_key: str | None = None
            for raw_declaration in module["declarations"]:
                declaration = require_keys(
                    raw_declaration,
                    {
                        "axioms", "include_in_statement", "kind", "material_file",
                        "name", "name_key",
                    },
                    "Inspector spool declaration",
                )
                name = declaration["name"]
                kind = declaration["kind"]
                name_key = declaration["name_key"]
                material_file = declaration["material_file"]
                include = declaration["include_in_statement"]
                if (not isinstance(name, str) or not name
                        or not isinstance(kind, str) or not kind
                        or not isinstance(name_key, str) or not name_key
                        or previous_name_key is not None and name_key <= previous_name_key
                        or not isinstance(material_file, str)
                        or not isinstance(include, bool)):
                    raise ValueError("Inspector spool declaration is malformed or unordered")
                previous_name_key = name_key
                if material_file in referenced_spools:
                    raise ValueError(f"statement material spool is reused: {material_file}")
                referenced_spools.add(material_file)
                material_path = regular_spool_file(spool, material_file)
                material = material_path.read_bytes()
                try:
                    material.decode("utf-8", errors="strict")
                except UnicodeDecodeError as error:
                    raise ValueError(
                        f"statement material spool is not strict UTF-8: {material_file}") from error
                type_sha256 = statement_address(material)
                declaration_preimage = canonical_json({
                    "declaration_name_key": name_key,
                    "kind": kind,
                    "module_path": source_path,
                    "schema": "declaration-statement-v1",
                    "statement_material": material.decode("utf-8"),
                })
                declaration_id = statement_address(declaration_preimage)
                destination = staged_materials / type_sha256[7:]
                if destination.exists():
                    if destination.read_bytes() != material:
                        raise ValueError(
                            f"statement material address collision: {type_sha256}")
                    material_path.unlink()
                else:
                    os.replace(material_path, destination)
                    material_bytes += len(material)
                declarations.append({
                    "axioms": require_sorted_strings(
                        declaration["axioms"], "Inspector spool declaration axioms"),
                    "include_in_statement": include,
                    "kind": kind,
                    "name": name,
                    "name_key": name_key,
                    "statement_id": declaration_id,
                    "type_sha256": type_sha256,
                })
                declaration_count += 1

            modules.append({
                "declarations": declarations,
                "imports": imports,
                "module": module_name,
                "source_path": source_path,
                "source_sha256": source_sha256,
            })

        actual_spools = {
            path.name for path in spool.iterdir()
            if path.is_file() or path.is_symlink()
        }
        if actual_spools:
            raise ValueError(
                "Inspector material spool has unreferenced files: "
                + ", ".join(sorted(actual_spools)))

        report_bytes = canonical_json({"modules": modules, "schema": REPORT_SCHEMA})
        staged_report = staged_root / "report.json"
        staged_report.write_bytes(report_bytes)
        staged_archive = staged_root / "materials.zip"
        with zipfile.ZipFile(
                staged_archive, "w", compression=zipfile.ZIP_DEFLATED,
                compresslevel=6, allowZip64=True) as archive:
            for source in sorted(staged_materials.iterdir(), key=lambda path: path.name):
                info = zipfile.ZipInfo(f"sha256/{source.name}", ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                with source.open("rb") as reader, archive.open(info, "w") as writer:
                    shutil.copyfileobj(reader, writer)
        live_materials = pathlib.Path(str(output) + ".materials.zip")
        legacy_materials = pathlib.Path(str(output) + ".materials")
        if legacy_materials.exists():
            shutil.rmtree(legacy_materials)
        live_materials.unlink(missing_ok=True)
        os.replace(staged_archive, live_materials)
        os.replace(staged_report, output)
        print(
            "LEAN_REPORT_MATERIALS "
            f"declarations={declaration_count} unique_bytes={material_bytes} "
            f"report_bytes={len(report_bytes)}"
        )
    finally:
        shutil.rmtree(staged_root, ignore_errors=True)


def main() -> int:
    if len(sys.argv) != 5 or sys.argv[1] != "compact":
        print(
            "usage: materials.py compact SPOOL_REPORT SPOOL_DIR OUTPUT",
            file=sys.stderr,
        )
        return 2
    try:
        compact(pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3]), pathlib.Path(sys.argv[4]))
        return 0
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"lean-report-materials: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
