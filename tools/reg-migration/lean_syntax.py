from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from .model import Registration, Root, Seal, Span, Template
from .snapshot import SnapshotError


KINDS = {"registration", "template", "root", "seal", "notation", "context"}
VARIANTS = {"legacy", "forward", "witness", "source", "finite-source", "occurrence", "native"}


def relative_reg_path(value: Any) -> str:
    if not isinstance(value, str):
        raise SnapshotError("invalid_source_path", repr(value))
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not value.startswith("Reg/") or path.suffix != ".lean":
        raise SnapshotError("invalid_source_path", value)
    return path.as_posix()


def source_module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def byte_slice(source: str, start: Any, end: Any, label: str) -> str:
    data = source.encode("utf-8")
    if type(start) is not int or type(end) is not int or not 0 <= start <= end <= len(data):
        raise SnapshotError("invalid_utf8_span", label)
    try:
        return data[start:end].decode("utf-8")
    except UnicodeDecodeError as error:
        raise SnapshotError("invalid_utf8_span", label) from error


def load_syntax_snapshot(path: Path | None, snapshot: dict[str, Any]) -> dict[str, Any]:
    if path is None:
        value = snapshot.get("syntax", snapshot)
    else:
        try:
            value = json.loads(path.read_bytes())
        except (OSError, ValueError) as error:
            raise SnapshotError("invalid_syntax_snapshot", str(error), str(path)) from error
    if not isinstance(value, dict) or not isinstance(value.get("files"), list):
        raise SnapshotError("missing_lean_syntax_snapshot", "Lean parser snapshot files are required")
    return value


def syntax_sources(snapshot: dict[str, Any]) -> dict[str, str]:
    sources: dict[str, str] = {}
    for file in snapshot.get("files", []):
        if not isinstance(file, dict):
            raise SnapshotError("invalid_syntax_file", repr(file))
        path = relative_reg_path(file.get("path"))
        if path in sources:
            raise SnapshotError("duplicate_source_file", path)
        source = file.get("source_text")
        if not isinstance(source, str):
            raise SnapshotError("missing_parser_source", path)
        digest = file.get("source_sha256")
        actual = hashlib.sha256(source.encode("utf-8")).hexdigest()
        if digest is not None and digest != actual:
            raise SnapshotError("syntax_source_sha_mismatch", path)
        sources[path] = source
    return sources


def parse_repository(repo: Path, snapshot: dict[str, Any] | Path | None = None) -> tuple[list[Registration], list[Template], list[Root], list[Seal], list[tuple[Path, Span, str]]]:
    """Consume Lean AST readouts; no source command or nested term parsing occurs here."""
    if snapshot is None:
        raise SnapshotError("missing_lean_syntax_snapshot", "parse_repository requires Lean parser output")
    if isinstance(snapshot, Path):
        snapshot = load_syntax_snapshot(snapshot, {})
    sources = syntax_sources(snapshot)
    registrations: list[Registration] = []
    templates: list[Template] = []
    roots: list[Root] = []
    seals: list[Seal] = []
    notations: list[tuple[Path, Span, str]] = []
    for file in sorted(snapshot["files"], key=lambda item: item["path"]):
        relative = file["path"]
        path, source = repo / relative, sources[relative]
        commands = file.get("commands")
        if not isinstance(commands, list):
            raise SnapshotError("missing_parser_commands", relative)
        intervals: list[tuple[int, int]] = []
        for command in sorted(commands, key=lambda item: item.get("start", -1)):
            kind = command.get("kind")
            if kind not in KINDS:
                raise SnapshotError("unknown_syntax", str(command.get("syntax_kind", kind)), relative)
            start, end = command.get("start"), command.get("end")
            body = byte_slice(source, start, end, relative)
            if start == end:
                raise SnapshotError("invalid_utf8_span", "empty command", relative)
            if any(start < right and left < end for left, right in intervals):
                raise SnapshotError("overlapping_commands", relative)
            intervals.append((start, end))
            slots: dict[str, str] = {}
            for name, slot in (command.get("slots") or {}).items():
                if not isinstance(slot, dict):
                    raise SnapshotError("invalid_slot", name, relative)
                left, right = slot.get("start"), slot.get("end")
                text = byte_slice(source, left, right, name)
                if not start <= left <= right <= end:
                    raise SnapshotError("slot_outside_command", name, relative)
                if slot.get("text") is not None and slot["text"] != text:
                    raise SnapshotError("slot_source_mismatch", name, relative)
                slots[name] = text
            span = Span(start, end)
            ambient_universes = command.get("ambient_universes", [])
            if not isinstance(ambient_universes, list) or any(not isinstance(level, str) or not level for level in ambient_universes) or len(set(ambient_universes)) != len(ambient_universes):
                raise SnapshotError("invalid_ambient_universes", relative)
            scope_wrappers = command.get("scope_wrappers", [])
            if not isinstance(scope_wrappers, list):
                raise SnapshotError("invalid_scope_wrapper", relative)
            for wrapper in scope_wrappers:
                if not isinstance(wrapper, dict) or type(wrapper.get("end")) is not int or wrapper["end"] > start:
                    raise SnapshotError("invalid_scope_wrapper", relative)
                prefix = byte_slice(source, wrapper.get("start"), wrapper.get("end"), "scope wrapper")
                if not prefix or wrapper.get("text") != prefix:
                    raise SnapshotError("scope_wrapper_source_mismatch", relative)
            parser_metadata = {"parser_slots": slots,
                               "parser_slot_spans": {name: {"start": slot["start"], "end": slot["end"]} for name, slot in (command.get("slots") or {}).items()},
                               "parser_slot_identifiers": {name: slot.get("identifiers", []) for name, slot in (command.get("slots") or {}).items()},
                               "parser_slot_universes": {name: slot.get("universe_occurrences", []) for name, slot in (command.get("slots") or {}).items()},
                               "namespace": command.get("namespace", ""),
                               "ambient_universes": ambient_universes, "scope_wrappers": scope_wrappers,
                               "scope_prefix": byte_slice(source, min(wrapper["start"] for wrapper in scope_wrappers), start, "scope prefix") if scope_wrappers else ""}
            if kind == "registration":
                variant = command.get("variant", "legacy")
                if variant not in VARIANTS:
                    raise SnapshotError("unknown_registration_shape", str(variant), relative)
                item = Registration(path, span, slots.get("theorem", ""), slots.get("arena", ""), variant=variant, source_text=body)
                for field in ("object_arena", "catalog", "primitive", "realization", "variation", "sensitivity", "readout", "output_evidence", "escape_from", "escape_from_source", "continuation", "source_record", "finite_bridge"):
                    setattr(item, field, slots.get(field))
                if "inline_actual" in slots and "inline_proof" in slots:
                    item.inline_bridge = (slots["inline_actual"], slots["inline_proof"])
                item.statement, item.proof = slots.get("target_type"), slots.get("native_proof")
                item.via_descriptor = slots.get("via_descriptor")
                item.native, item.occurrence = variant == "native", variant == "occurrence"
                item.source, item.finite_source = variant == "source", variant == "finite-source"
                item.snapshot = {**parser_metadata, "variant": variant}
                registrations.append(item)
            elif kind == "template":
                item = Template(path, span, slots.get("name", ""), source_text=body)
                item.snapshot = parser_metadata
                templates.append(item)
            elif kind == "root":
                item = Root(path, span, source_module(relative), [], [], [], None)
                item.snapshot = parser_metadata
                roots.append(item)
            elif kind == "seal":
                item = Seal(path, span, source_module(relative))
                item.snapshot = parser_metadata
                seals.append(item)
            elif kind == "notation":
                notations.append((path, span, body))
    return registrations, templates, roots, seals, notations
