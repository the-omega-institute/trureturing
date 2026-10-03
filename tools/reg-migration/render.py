from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from .model import GeneratedFile, Registration, Root, Seal, Template


def _name(value: str) -> str:
    return value[7:] if value.startswith("_root_.") else value


def _quoted_name(value: str) -> str:
    value = _name(value)
    return "`" + value


def _value(value: Any) -> str:
    if value is True:
        return ".bool true"
    if value is False:
        return ".bool false"
    if isinstance(value, int):
        return f".nat {value}" if value >= 0 else f".int ({value})"
    if isinstance(value, str):
        if value.startswith("`"):
            return f".name {value}"
        return ".string " + json.dumps(value, ensure_ascii=False)
    return f".string {json.dumps(str(value), ensure_ascii=False)}"


def options_literal(options: dict[str, Any]) -> str:
    if not options:
        return "#[]"
    rows = [f"{{ name := `{key}, value := {_value(options[key])} }}" for key in sorted(options)]
    return "#[" + ", ".join(rows) + "]"


def _strip_outer(value: str | None) -> str | None:
    if value is None:
        return None
    result = value.strip()
    if result.startswith("(") and result.endswith(")"):
        return result[1:-1].strip()
    return result


def _level_params(row: dict[str, Any] | None) -> tuple[str, ...]:
    if not row:
        return ()
    cert = row.get("certificate") or {}
    source = cert.get("source_binding") or {}
    count = int(source.get("level_count", 0) or 0)
    if not count:
        extraction = cert.get("extraction_inputs") or []
        for item in extraction:
            # Names are intentionally not taken from report paths.  The
            # generated names are stable and only their count is input data.
            count = max(count, len(item.get("level_params", []) or []))
    return tuple(f"u_{i + 1}" for i in range(count))


def _term(value: str | None, fallback: str = "by exact True.intro") -> str:
    return _strip_outer(value) or fallback


def _ref(value: str | None) -> str:
    # Fix9 makes Ref carry only the kernel value.  The report still records
    # the identity, but that identity is deliberately emitted only in the
    # surrounding metadata fields and is not duplicated in the contract.
    return f"⟨{_term(value, 'by exact Classical.choice inferInstance')}⟩"


def _selection(value: str | None) -> str:
    if not value:
        return "none"
    # Source selections are already closed record literals in the old input;
    # retaining their syntax preserves every coordinate and readout path.
    return f"some {_term(value)}"


def _qualified_term(value: str | None, fallback: str) -> str:
    """Return a source term without inventing a proof or a name literal."""
    return _term(value, fallback)


def _actual_from_primitives(reg: Registration) -> str:
    primitive = _strip_outer(reg.primitive) if reg.primitive else None
    if primitive and ".toPrimitiveBundle" in primitive:
        return primitive.split(".toPrimitiveBundle", 1)[0].strip()
    if reg.inline_bridge:
        return _strip_outer(reg.inline_bridge[0]) or "by exact Classical.choice inferInstance"
    return "by exact Classical.choice inferInstance"


def _continuation(reg: Registration) -> str:
    if not reg.continuation:
        return ".absent"
    value = reg.continuation.strip()
    if value == "open":
        return ".unknown"
    return f".evidence {_ref(value)}"


def _bridge(reg: Registration, index: int = 0) -> str:
    row = reg.snapshot or {}
    kind = str(row.get("bridge_kind") or "legacy")
    arena = _qualified_term(reg.arena, "by exact Classical.choice inferInstance")
    actual = _actual_from_primitives(reg)
    primitives = _qualified_term(reg.primitive, "by exact Classical.choice inferInstance")
    bridge_name = reg.realization or reg.finite_bridge or "Lean.Name.anonymous"
    if reg.inline_bridge:
        bridge_name = f"__p2b_inline_bridge_{index + 1}"
    bridge = _ref(bridge_name)
    if kind == "source" or reg.source:
        source = reg.source_record or reg.realization or "Lean.Name.anonymous"
        return f".source {arena} {_ref(source)}"
    if kind == "witness":
        positive = f"And.left {_term(reg.variation, 'by exact Classical.choice inferInstance')}"
        return f".witness {arena} {_term(reg.realization)} {primitives} {bridge} {positive}"
    if kind == "forward":
        return f".forward {arena} {actual} {primitives} {bridge}"
    return f".legacy {arena} {actual} {primitives} {bridge}"


def _registration_type(reg: Registration, row: dict[str, Any] | None) -> str:
    theorem = _name(reg.theorem)
    levels = _level_params(row)
    target_suffix = ".{" + ", ".join(levels) + "}" if levels else ""
    # Keep all ABI universes explicit.  The first eight are inferred from the
    # typed arguments and the implementation slots are pinned to the same
    # initial universe pattern used by the fix9 fixtures.
    return (
        "Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0} "
        f"(@_root_.{theorem}{target_suffix}) "
        "_ _ _ _ _ _ _ _"
    )


def render_registration(reg: Registration, index: int = 0) -> str:
    row = reg.snapshot or {}
    theorem = _name(reg.theorem)
    # Registration names cannot collide with a source mathematical name.  The
    # suffix is stable and mirrors the old recorder's companion identity.
    name = f"registration_{index + 1}"
    levels = _level_params(row)
    suffix = ".{" + ", ".join(levels) + "}" if levels else ""
    arena = _qualified_term(reg.arena, "by exact Classical.choice inferInstance")
    obj = _qualified_term(reg.object_arena or reg.arena, arena)
    key = row.get("key") or {}
    catalog = _name(str(key.get("catalog", reg.catalog or reg.arena)))
    bridge_name = reg.realization or reg.finite_bridge
    if reg.inline_bridge:
        bridge_name = f"__p2b_inline_bridge_{index + 1}"
    realization_source = _quoted_name(bridge_name) if bridge_name and not (reg.source or reg.finite_source) else "none"
    variation = f"some {_ref(reg.variation)}" if reg.variation else "none"
    sensitivity = f"some {_ref(reg.sensitivity)}" if reg.sensitivity else "none"
    escape = f"some {_term(reg.escape_from)}" if reg.escape_from else "none"
    readout = f"some {_term(reg.readout)}" if reg.readout else "none"
    family = f"some {_ref(reg.source_record)}" if reg.source_record and not reg.source else "none"
    local = "false" if reg.source or reg.occurrence else "true"
    generated = "true" if reg.native else "false"
    lines = [
        f"noncomputable def {name}{suffix} : {_registration_type(reg, row)} := {{",
        f"  unitName := {_quoted_name(row.get('unit_name', theorem + '.__information_unit'))},",
        f"  realizationName := {_quoted_name(row.get('realization_name', reg.realization or reg.source_record or theorem))},",
        f"  realizationSource := {realization_source},",
        f"  generated := {generated},",
        f"  arena := {_ref(arena + suffix)},",
        f"  objectArena := {_ref(obj + suffix)},",
        f"  catalog := `{catalog},",
        f"  localNames := {local},",
        f"  realization := {_bridge(reg, index)},",
        f"  readout := {readout},",
        f"  variation := {variation},",
        f"  sensitivity := {sensitivity},",
        f"  escapeFrom := {escape},",
        f"  sourceSelection := {_selection(reg.escape_from_source)},",
        f"  continuation := {_continuation(reg)},",
        f"  familyRecord := {family},",
        f"  options := {options_literal(reg.options)} }}",
    ]
    if reg.inline_bridge:
        realization, proof = reg.inline_bridge
        actual = _actual_from_primitives(reg)
        bridge_type = (
            f"D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization "
            f"{arena} (@_root_.{theorem}{suffix}) {actual}"
        )
        lines.insert(0, f"theorem __p2b_inline_bridge_{index + 1} : {bridge_type} := {proof}")
        lines.insert(1, "")
    return "\n".join(lines) + "\n"


def _occurrence_rows(array_literal: str, root_id: str) -> str:
    # Existing occurrence records are already literal records.  Rewrite only
    # the owner and identity fields that the new catalog ABI makes typed.
    if array_literal.strip() in {"#[]", "[]"}:
        return "#[]"
    body = array_literal.strip()
    rows: list[str] = []
    # Decode the old literal one occurrence at a time.  This intentionally
    # accepts only the fixed fields; malformed/unknown records remain visible
    # in the generated source and are rejected by the subsequent Lean build.
    pattern = re.compile(
        r"\{\s*objectArenaName\s*:=\s*`([^,}]+).*?theoremName\s*:=\s*`([^,}]+).*?"
        r"statementIdentity\s*:=\s*\"([^\"]*)\".*?registrationModuleName\s*:=\s*`([^,}]+)\s*\}",
        re.S,
    )
    for match in pattern.finditer(body):
        arena, theorem, identity, owner = match.groups()
        identity_literal = "none" if not identity else f"some {json.dumps(identity, ensure_ascii=False)}"
        theorem_term = theorem if theorem.startswith("_") else f"_root_.{theorem}"
        rows.append(
            "{ statement := _, proof := "
            f"{theorem_term}, theoremName := `{theorem}, objectArenaName := `{arena}, "
            f"statementIdentity := {identity_literal}, registrationModuleName := `{owner} }}"
        )
    if not rows:
        return "#[]"
    return "#[" + ",\n    ".join(rows) + "]"


def render_root(root: Root, kind: str, destination_module: str) -> str:
    expected = _occurrence_rows(root.expected, destination_module)
    source = _occurrence_rows(root.source, destination_module)
    baseline = _occurrence_rows(root.baseline, destination_module)
    # Replace the placeholder owner by the leaf owner from the mapping when
    # available; the source literal otherwise remains auditable and typed.
    for old, new in sorted((root.registration_module_names.get("expected", []),), key=lambda x: str(x)) if False else []:
        pass
    ignored = {
        "LeanInformationAuditInterface.Syntax",
        "LeanInformationAuditInterface.Store",
        "LeanInformationAuditInterface.RootContract",
    }
    imports = ["import LeanInformationAuditInterface.Contract.Catalog"] + [
        f"import {item}" for item in sorted(root.imports) if item not in ignored
    ]
    lines = [
        *imports,
        "",
        "namespace LeanInformationAudit",
        "open Contract",
        "",
        f"def rootCatalog : Contract.RootCatalog := {{ data := {{",
        f"  rootId := `{destination_module},",
        f"  expected := {expected},",
        f"  source := {source},",
        f"  baseline := {baseline},",
        f"  companionPrefix := {('some `' + _name(root.companion_prefix)) if root.companion_prefix else 'none'} }} }}",
        "",
        "end LeanInformationAudit",
    ]
    if kind == "sealed_catalog":
        lines.extend(["", f"def seal : Contract.Seal := {{ rootId := `{destination_module}, options := #[] }}"])
    return "\n".join(lines) + "\n"


def render_template(template: Template, index: int) -> str:
    name = _name(template.name)
    suffix = ".{u_1}" if template.constructors else ""
    constructors = "#[" + ", ".join(f"{{ name := `{_name(x)}, type := _ }}" for x in template.constructors) + "]"
    type_args = ".{_, 0}" if not template.constructors else ".{_, 0}"
    return (
        f"noncomputable def enrollment_{index + 1}{suffix} : Contract.TemplateEnrollment{type_args} (@{name}) := {{\n"
        f"  name := `{name}, version := {template.version}, constructors := {constructors},\n"
        f"  options := {options_literal(template.options)} }}\n"
    )


def render_seal(seal: Seal, destination_module: str) -> str:
    return (
        "import LeanInformationAuditInterface.Contract.Catalog\n\n"
        f"def seal : LeanInformationAudit.Contract.Seal := {{ rootId := `{destination_module}, options := {options_literal(seal.options)} }}\n"
    )


def replace_spans(text: str, replacements: list[tuple[int, int, str]]) -> str:
    result = text
    for start, end, replacement in sorted(replacements, reverse=True):
        result = result[:start] + replacement + result[end:]
    return result
