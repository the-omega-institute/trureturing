from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_report(path: Path) -> tuple[dict[str, Any], str]:
    raw = path.read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def _rows(report: dict[str, Any], key: str) -> Iterable[dict[str, Any]]:
    for module in report.get("modules", []):
        evidence = module.get("information_templates") or {}
        values = evidence.get(key) or []
        if isinstance(values, dict):
            values = values.get("records", [])
        for row in values:
            if isinstance(row, dict):
                yield row


def registration_rows(report: dict[str, Any]) -> list[dict[str, Any]]:
    return list(_rows(report, "records"))


def row_key(row: dict[str, Any]) -> tuple[str, str, str, str, str]:
    key = row.get("key") or {}
    return tuple(str(key.get(k, "")) for k in ("root", "registration_module", "theorem", "object_arena", "catalog"))  # type: ignore[return-value]


def index_rows(rows: Iterable[dict[str, Any]]) -> tuple[dict[tuple[str, str, str, str, str], dict[str, Any]], list[tuple[str, dict[str, Any]]]]:
    index: dict[tuple[str, str, str, str, str], dict[str, Any]] = {}
    duplicates: list[tuple[str, dict[str, Any]]] = []
    for row in rows:
        key = row_key(row)
        if key in index:
            duplicates.append(("duplicate", row))
        else:
            index[key] = row
    return index, duplicates


def load_input_snapshot(path: Path | None) -> dict[str, Any]:
    if path is None:
        return {}
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("input snapshot must be a JSON object")
    return value

