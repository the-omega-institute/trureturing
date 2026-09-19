#!/usr/bin/env python3
"""Compact Inspector statement spools into the canonical v2 report bundle."""

from __future__ import annotations

import gzip
import hashlib
import codecs
import json
import os
import pathlib
import re
import shutil
import stat
import sys
import tempfile
import time
import zipfile
from typing import BinaryIO, Iterable


SPOOL_SCHEMA = "stratalint-lean-inspector-spool-v1"
REPORT_SCHEMA = "stratalint-raw-lean-report-v2"
STATEMENT_DOMAIN = b"trureturing:statement:v1\0"
MATERIAL_FILE = re.compile(r"^[0-9]+\.statement(?:\.gz)?$")
HEX = re.compile(r"[0-9a-f]{64}")
SUPPLEMENTARY_SCALAR = re.compile(r"[\U00010000-\U0010FFFF]")
ARCHIVE_TIMESTAMP = (1980, 1, 1, 0, 0, 0)
BUFFER_BYTES = 64 * 1024


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
    return _statement_address((material,))


def _statement_address(blocks: Iterable[bytes]) -> str:
    digest = hashlib.sha256(STATEMENT_DOMAIN)
    for block in blocks:
        digest.update(block)
    return "sha256:" + digest.hexdigest()


def verify_material(source: BinaryIO, address: str, target: BinaryIO | None = None) -> None:
    """Verify a material stream, optionally copying it into a private staging sink."""
    def blocks() -> Iterable[bytes]:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            if target is not None:
                target.write(block)
            yield block

    if _statement_address(blocks()) != address:
        raise ValueError(f"statement material address mismatch: {address}")


def declaration_statement_id(source_path: str, kind: str, name_key: str, material: str) -> str:
    """The canonical declaration address used by the report and ownership query."""
    return statement_address(canonical_json({
        "declaration_name_key": name_key,
        "kind": kind,
        "module_path": source_path,
        "schema": "declaration-statement-v1",
        "statement_material": material,
    }))


def material_identities(source: BinaryIO, source_path: str, kind: str, name_key: str,
                        chunk_size: int = BUFFER_BYTES) -> tuple[str, str]:
    """Hash both identities in one bounded, strictly decoded UTF-8 pass.

    The canonical declaration JSON has its material as its last field. JSON
    escaping is scalar-local; the incremental decoder retains only an incomplete
    UTF-8 scalar between reads, including at EOF.
    """
    prefix = canonical_json({
        "declaration_name_key": name_key, "kind": kind, "module_path": source_path,
        "schema": "declaration-statement-v1", "statement_material": "",
    })[:-3]
    raw = hashlib.sha256(STATEMENT_DOMAIN)
    declaration = hashlib.sha256(STATEMENT_DOMAIN + prefix)
    decoder = codecs.getincrementaldecoder("utf-8")("strict")
    while True:
        block = source.read(chunk_size)
        raw.update(block)
        text = decoder.decode(block, final=not block)
        if text:
            # Use the same string encoder as JSONEncoder without constructing
            # an encoder for each chunk. Only supplementary scalars need the
            # canonical surrogate rewrite. UTF-16 counts them in native code,
            # avoiding a regex scan of every ordinary ASCII/BMP material.
            encoded = json.encoder.encode_basestring(text)[1:-1]
            if not text.isascii() and len(text.encode("utf-16-le")) != 2 * len(text):
                encoded = SUPPLEMENTARY_SCALAR.sub(escape_supplementary_scalar, encoded)
            declaration.update(encoded.encode("utf-8"))
        if not block:
            break
    declaration.update(b'"}\n')
    return "sha256:" + raw.hexdigest(), "sha256:" + declaration.hexdigest()


def streams_equal(left: BinaryIO, right: BinaryIO) -> bool:
    while True:
        block = left.read(BUFFER_BYTES)
        if block != right.read(BUFFER_BYTES):
            return False
        if not block:
            return True


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


def validate_family_registration(value: object, context: str) -> None:
    """Validate the native source/declaration relation before compacting it."""
    family = require_keys(value, {
        "schema", "owner", "type_identity", "body_identity", "registration_identity",
        "level_arity", "family_relation",
    }, context)
    if (family["schema"] != "dtr-family-declaration-v1"
            or any(not isinstance(family[field], str) or not family[field]
                   for field in ("owner",))
            or any(not isinstance(family[field], str)
                   or not HEX.fullmatch(family[field])
                   for field in ("type_identity", "body_identity", "registration_identity"))
            or type(family["level_arity"]) is not int
            or family["level_arity"] < 0 or family["level_arity"] > 64):
        raise ValueError(f"{context} is malformed")
    relation = family["family_relation"]
    if relation is None:
        return
    relation = require_keys(relation, {
        "mode", "source_name", "source_statement_identity", "arena_name",
        "arena_identity", "law_identity", "registration_name", "exact_source_law",
    }, context + " relation")
    if (relation["mode"] != "dependent-family-v1"
            or any(not isinstance(relation[field], str) or not relation[field]
                   for field in ("source_name", "arena_name", "registration_name"))
            or any(not isinstance(relation[field], str) or not HEX.fullmatch(relation[field])
                   for field in ("source_statement_identity", "arena_identity", "law_identity"))
            or type(relation["exact_source_law"]) is not bool):
        raise ValueError(f"{context} relation is malformed")


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


def open_material(path: pathlib.Path):
    return gzip.open(path, "rb") if path.name.endswith(".gz") else path.open("rb")


def read_material(path: pathlib.Path) -> bytes:
    with open_material(path) as reader:
        return reader.read()


def stream_spool(spool: pathlib.Path) -> None:
    """One writer process; acknowledgments delimit completed compressed files."""
    spool.mkdir(parents=True, exist_ok=True)
    index = 0
    while True:
        header = sys.stdin.buffer.readline()
        if header == b"done\n":
            print("done", flush=True)
            return
        chunked = header == b"chunks\n"
        if not chunked and not re.fullmatch(rb"[1-9][0-9]*\n", header):
            raise ValueError("invalid or missing material frame length")
        remaining = 0 if chunked else int(header)
        path = spool / f"{index}.statement.gz"
        temporary = spool / f"{index}.statement.gz.tmp"
        try:
            with temporary.open("xb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                                   compresslevel=6, mtime=0) as writer:
                    total = 0
                    while True:
                        if chunked:
                            size = sys.stdin.buffer.readline(32)
                            if not re.fullmatch(rb"(?:0|[1-9][0-9]*)\n", size):
                                raise ValueError("invalid or missing material chunk length")
                            remaining = int(size)
                            if remaining > BUFFER_BYTES:
                                raise ValueError("material chunk exceeds writer buffer")
                        if not remaining:
                            if not total:
                                raise ValueError("empty material frame")
                            break
                        while remaining:
                            block = sys.stdin.buffer.read(min(remaining, BUFFER_BYTES))
                            if not block:
                                raise ValueError("truncated material frame")
                            writer.write(block)
                            remaining -= len(block)
                            total += len(block)
                        if not chunked:
                            break
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)
        index += 1
        print("ok", flush=True)


def read_manifest_version(manifest: pathlib.Path) -> int:
    def unique_fields(pairs):
        fields = {}
        for key, value in pairs:
            if key in fields:
                raise ValueError("duplicate manifest field")
            fields[key] = value
        return fields
    try:
        data = json.loads(pathlib.Path(manifest).read_text(encoding="utf-8"), object_pairs_hook=unique_fields)
        version = data["report_semantic_version"]
        if type(version) is not int or version <= 0:
            raise ValueError("positive integer required")
        return version
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as error:
        raise ValueError("DTR-ManifestVersion: lean-report-inputs.json requires a positive integer report_semantic_version") from error


def validate_template_evidence(value: object, manifest: pathlib.Path) -> None:
    version = read_manifest_version(manifest)
    if isinstance(value, dict) and type(value.get("compatibility_version")) is not int:
        raise ValueError("DTR-EvidenceVersion: Inspector declared-template evidence compatibility_version requires a positive integer")
    evidence = require_keys(value,
        {"schema_version", "compatibility_version", "inventory", "registered", "records", "inputs"},
        "Inspector declared-template evidence")
    if (type(evidence["schema_version"]) is not int or evidence["schema_version"] != 1
            or any(not isinstance(evidence[field], list)
                   for field in ("inventory", "registered", "records", "inputs"))):
        raise ValueError("Inspector declared-template evidence is malformed")
    if evidence["compatibility_version"] != version:
        raise ValueError("DTR-EvidenceVersion: Inspector declared-template evidence compatibility_version differs from report_semantic_version")


def compact(spool_report: pathlib.Path, spool: pathlib.Path, output: pathlib.Path,
            manifest: pathlib.Path) -> None:
    started = time.perf_counter_ns()
    read_manifest_version(manifest)
    root = json.loads(spool_report.read_text(encoding="utf-8"))
    require_keys(root, {"modules", "schema"}, "Inspector spool")
    if root["schema"] != SPOOL_SCHEMA or not isinstance(root["modules"], list):
        raise ValueError("Inspector spool schema is invalid")

    output.parent.mkdir(parents=True, exist_ok=True)
    staged_root = pathlib.Path(tempfile.mkdtemp(prefix=".lean-materials.", dir=output.parent))
    material_sources: dict[str, pathlib.Path] = {}
    referenced_spools: set[str] = set()
    modules: list[dict] = []
    previous_module: str | None = None
    declaration_count = 0
    material_bytes = 0
    try:
        for raw_module in root["modules"]:
            module_keys = {"declarations", "imports", "module", "source_path", "source_sha256"}
            if "information_registration_errors" in raw_module:
                module_keys.add("information_registration_errors")
            if "information_templates" in raw_module:
                module_keys.add("information_templates")
            if "utility_refutation" in raw_module:
                module_keys.add("utility_refutation")
            module = require_keys(
                raw_module,
                module_keys,
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
            registration_errors = module.get("information_registration_errors")
            if registration_errors is not None and (
                    not isinstance(registration_errors, list)
                    or any(not isinstance(item, str) for item in registration_errors)
                    or registration_errors != sorted(set(registration_errors))):
                raise ValueError("Inspector registration evidence is malformed")
            information_templates = module.get("information_templates")
            if information_templates is not None:
                validate_template_evidence(information_templates, manifest)
            refutation = module.get("utility_refutation")
            if refutation is not None:
                require_keys(refutation, {"claim_gid", "claim_source_path", "claim_source_sha256", "result_gid", "is_closed_negation"},
                             "Inspector refutation")
                if (not isinstance(refutation["claim_gid"], str) or not refutation["claim_gid"]
                        or not isinstance(refutation["result_gid"], str) or not refutation["result_gid"]
                        or not isinstance(refutation["claim_source_path"], str) or not refutation["claim_source_path"]
                        or not isinstance(refutation["claim_source_sha256"], str)
                        or not re.fullmatch(r"sha256:[0-9a-f]{64}", refutation["claim_source_sha256"])
                        or not isinstance(refutation["is_closed_negation"], bool)):
                    raise ValueError("Inspector refutation is malformed")
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
                    } | ({"family_registration"} if isinstance(raw_declaration, dict)
                         and "family_registration" in raw_declaration else set()),
                    "Inspector spool declaration",
                )
                if "family_registration" in declaration:
                    validate_family_registration(declaration["family_registration"],
                                                 "Inspector family declaration")
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

                try:
                    with open_material(material_path) as source:
                        type_sha256, declaration_id = material_identities(source, source_path, kind, name_key)
                        decoded_bytes = source.tell()
                except UnicodeDecodeError as error:
                    raise ValueError(
                        f"statement material spool is not strict UTF-8: {material_file}") from error
                address = type_sha256[7:]
                if address in material_sources:
                    with open_material(material_sources[address]) as left, open_material(material_path) as right:
                        if not streams_equal(left, right):
                            raise ValueError(f"statement material address collision: {type_sha256}")
                else:
                    material_sources[address] = material_path
                    material_bytes += decoded_bytes
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
                if "family_registration" in declaration:
                    declarations[-1]["family_registration"] = declaration["family_registration"]
                declaration_count += 1

            report_module = {
                "declarations": declarations,
                "imports": imports,
                "module": module_name,
                "source_path": source_path,
                "source_sha256": source_sha256,
            }
            if registration_errors is not None:
                report_module["information_registration_errors"] = registration_errors
            if information_templates is not None:
                report_module["information_templates"] = information_templates
            if refutation is not None:
                report_module["utility_refutation"] = refutation
            modules.append(report_module)

        actual_spools = {
            path.name for path in spool.iterdir()
            if path.is_file() or path.is_symlink()
        }
        if actual_spools != referenced_spools:
            raise ValueError(
                "Inspector material spool has unreferenced files: "
                + ", ".join(sorted(actual_spools.symmetric_difference(referenced_spools))))

        report_bytes = canonical_json({"modules": modules, "schema": REPORT_SCHEMA})
        staged_report = staged_root / "report.json"
        staged_report.write_bytes(report_bytes)
        staged_archive = staged_root / "materials.zip"
        with zipfile.ZipFile(
                staged_archive, "w", compression=zipfile.ZIP_DEFLATED,
                compresslevel=6, allowZip64=True) as archive:
            for address, source in sorted(material_sources.items()):
                info = zipfile.ZipInfo(f"sha256/{address}", ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                digest = hashlib.sha256(STATEMENT_DOMAIN)
                with open_material(source) as reader, archive.open(info, "w") as writer:
                    while block := reader.read(64 * 1024):
                        digest.update(block)
                        writer.write(block)
                if digest.hexdigest() != address:
                    raise ValueError("statement material changed during compaction")
        live_materials = pathlib.Path(str(output) + ".materials.zip")
        legacy_materials = pathlib.Path(str(output) + ".materials")
        # Some callers spool directly into the legacy output directory. Remove
        # consumed inputs before removing that directory (or one containing it).
        for relative in referenced_spools:
            (spool / relative).unlink()
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
        if os.environ.get("STRATALINT_INSPECTOR_PROFILE") == "1":
            import resource
            rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            if sys.platform != "darwin":
                rss *= 1024
            print(f"LEAN_INSPECTOR_PROFILE compact_ns={time.perf_counter_ns() - started} max_process_rss_bytes={rss}")
    finally:
        shutil.rmtree(staged_root, ignore_errors=True)


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "stream":
        try:
            stream_spool(pathlib.Path(sys.argv[2]))
            return 0
        except (OSError, ValueError) as error:
            print(f"lean-report-materials: {error}", file=sys.stderr)
            return 1
    if len(sys.argv) != 6 or sys.argv[1] != "compact":
        print(
            "usage: materials.py compact SPOOL_REPORT SPOOL_DIR OUTPUT MANIFEST | stream SPOOL_DIR",
            file=sys.stderr,
        )
        return 2
    try:
        compact(pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3]), pathlib.Path(sys.argv[4]),
                pathlib.Path(sys.argv[5]))
        return 0
    except (OSError, EOFError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"lean-report-materials: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
