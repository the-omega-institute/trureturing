from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


class SnapshotError(ValueError):
    def __init__(self, code: str, detail: str, path: str = ""):
        super().__init__(detail)
        self.code, self.detail, self.path = code, detail, path


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_input_snapshot(path: Path) -> tuple[dict[str, Any], str]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, ValueError) as error:
        raise SnapshotError("invalid_input_snapshot", str(error), str(path)) from error
    if not isinstance(value, dict):
        raise SnapshotError("invalid_input_snapshot", "input snapshot must be a JSON object", str(path))
    if value.get("schema") not in {"reg-migration-inputs-v2", "reg-migration-inputs-v1"}:
        raise SnapshotError("unknown_input_schema", str(value.get("schema")), str(path))
    for category in ("registrations", "templates", "roots", "seals"):
        rows = value.get(category)
        if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
            raise SnapshotError("missing_input_category", category, str(path))
    return value, hashlib.sha256(raw).hexdigest()


def typed_options(value: Any) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        raise SnapshotError("missing_compiled_options", "Options must be a compiled typed array")
    options: list[dict[str, Any]] = []
    seen: set[str] = set()
    for item in value:
        if not isinstance(item, dict):
            raise SnapshotError("invalid_option", repr(item))
        name, kind, setting = item.get("name"), item.get("type"), item.get("value")
        if not isinstance(name, str) or not name or name in seen:
            raise SnapshotError("duplicate_option" if name in seen else "invalid_option", repr(name))
        valid = ((kind == "bool" and type(setting) is bool)
                 or (kind == "nat" and type(setting) is int and setting >= 0)
                 or (kind == "int" and type(setting) is int)
                 or (kind in {"string", "name"} and isinstance(setting, str)))
        if not valid:
            raise SnapshotError("unsupported_option_type", repr(item))
        seen.add(name)
        encoded = {"name": name, "type": kind, "value": setting}
        for key in ("name_components", "value_components"):
            if key in item:
                encoded[key] = item[key]
        options.append(encoded)
    return sorted(options, key=lambda item: item["name"])


def closed_printed_term(value: Any, field: str) -> str | None:
    if value is None:
        return None
    if not isinstance(value, dict) or value.get("printed") is not True:
        raise SnapshotError("uncontrolled_expression", field)
    text = value.get("text")
    if not isinstance(text, str) or not text.strip():
        raise SnapshotError("expression_print_failed", field)
    if value.get("closed") is False or value.get("has_mvars") is True or value.get("has_fvars") is True:
        raise SnapshotError("unclosed_expression", field)
    if "?m." in text or "?u." in text or "sorryAx" in text:
        raise SnapshotError("unclosed_expression", field)
    return text


def validate_level_params(row: dict[str, Any], label: str) -> None:
    original, extra = row.get("level_params", []), row.get("extra_level_params", [])
    for values in (original, extra):
        if not isinstance(values, list) or any(not isinstance(value, str) or not value for value in values):
            raise SnapshotError("invalid_level_params", label)
        if len(values) != len(set(values)):
            raise SnapshotError("duplicate_level_params", label)
    if set(original) & set(extra):
        raise SnapshotError("duplicate_level_params", label)


def validate_expression_levels(value: Any, declared: list[str], label: str) -> None:
    if not isinstance(value, dict) or value.get("printed") is not True:
        return
    if not isinstance(declared, list) or any(not isinstance(level, str) or not level for level in declared):
        raise SnapshotError("invalid_level_params", label)
    levels = value.get("level_params", [])
    if not isinstance(levels, list) or any(not isinstance(level, str) or not level for level in levels):
        raise SnapshotError("invalid_expression_levels", label)
    if len(levels) != len(set(levels)):
        raise SnapshotError("invalid_expression_levels", label)
    missing = sorted(set(levels) - set(declared))
    if missing:
        raise SnapshotError("missing_level_params", label + ":" + ",".join(missing))


def validate_universe_text(value: Any, label: str) -> None:
    if not isinstance(value, str) or not value.strip():
        raise SnapshotError("invalid_universe", label)
    tokens = value.replace("+", " ").split()
    if "?u." in value or "?m." in value or "?_mvar." in value or any(token.lstrip("(").startswith("?") or token.strip("()") == "_" for token in tokens):
        raise SnapshotError("unclosed_universe", label)


def type_arg_source_slots(row: dict[str, Any]) -> list[str | None]:
    sources = row.get("type_arg_source_slots", [None] * 8)
    if not isinstance(sources, list) or len(sources) != 8:
        raise SnapshotError("invalid_type_arg_source_slots", "expected eight source slots")
    allowed = ({"arena"}, {"object_arena", "arena"}, {"readout"}, {"variation"},
               {"sensitivity"}, {"escape_from"}, {"continuation"}, {"source_record"})
    slots = row.get("parser_slots", {})
    arguments = row.get("type_args", [])
    for index, source in enumerate(sources):
        if source is None:
            continue
        if not isinstance(source, str) or source not in allowed[index]:
            raise SnapshotError("invalid_type_arg_source_slots", f"type_args[{index}]")
        text = slots.get(source) if isinstance(slots, dict) else None
        if not isinstance(text, str) or not text.strip() or source == "continuation" and text.strip() == "open":
            raise SnapshotError("missing_type_arg_source", f"type_args[{index}]:{source}")
        if index >= len(arguments) or arguments[index] is not None:
            raise SnapshotError("type_arg_source_mismatch", f"type_args[{index}]:{source}")
    return sources
