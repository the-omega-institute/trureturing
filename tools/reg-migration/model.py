from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Span:
    start: int
    end: int


@dataclass
class Registration:
    path: Path
    span: Span
    theorem: str
    arena: str
    object_arena: str | None = None
    catalog: str | None = None
    primitive: str | None = None
    realization: str | None = None
    variation: str | None = None
    sensitivity: str | None = None
    readout: str | None = None
    output_evidence: str | None = None
    escape_from: str | None = None
    escape_from_source: str | None = None
    continuation: str | None = None
    source_record: str | None = None
    finite_bridge: str | None = None
    inline_bridge: tuple[str, str] | None = None
    native: bool = False
    occurrence: bool = False
    source: bool = False
    finite_source: bool = False
    options: dict[str, Any] = field(default_factory=dict)
    snapshot: dict[str, Any] | None = None

    @property
    def key(self) -> tuple[str, str, str, str, str]:
        row = self.snapshot or {}
        key = row.get("key", {})
        return (
            str(key.get("root", self.module_name)),
            str(key.get("registration_module", self.module_name)),
            str(key.get("theorem", self.theorem)),
            str(key.get("object_arena", self.object_arena or self.arena)),
            str(key.get("catalog", self.catalog or self.arena)),
        )

    @property
    def module_name(self) -> str:
        parts = self.path.with_suffix("").parts
        try:
            index = parts.index("Reg")
            return ".".join(parts[index:])
        except ValueError:
            return ".".join(parts)


@dataclass
class Template:
    path: Path
    span: Span
    name: str
    version: int = 1
    constructors: list[str] = field(default_factory=list)
    options: dict[str, Any] = field(default_factory=dict)


@dataclass
class Root:
    path: Path
    span: Span
    root_id: str
    expected: str
    source: str
    baseline: str
    companion_prefix: str | None
    kind: str = "catalog"
    destination_path: str | None = None
    destination_module: str | None = None
    registration_module_names: dict[str, list[str]] = field(default_factory=dict)
    imports: list[str] = field(default_factory=list)


@dataclass
class Seal:
    path: Path
    span: Span
    root_id: str
    options: dict[str, Any] = field(default_factory=dict)


@dataclass
class Failure:
    code: str
    path: str
    detail: str

    def as_dict(self) -> dict[str, str]:
        return {"code": self.code, "path": self.path, "detail": self.detail}


@dataclass
class GeneratedFile:
    path: str
    text: str
    kind: str


@dataclass
class PlanResult:
    input_sha256: str
    registrations: list[Registration]
    templates: list[Template]
    roots: list[Root]
    seals: list[Seal]
    files: list[GeneratedFile]
    failures: list[Failure]
    audit: dict[str, Any]
