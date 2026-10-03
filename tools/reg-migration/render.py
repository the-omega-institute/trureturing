from __future__ import annotations

import json
from typing import Any

from .model import Registration, Root, Seal, Template


def _name(value: str) -> str:
    return value.removeprefix("_root_.")


def _quoted_name(value: str) -> str:
    return "`" + _name(value) if value else "Lean.Name.anonymous"


def _string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def _expression(value: Any) -> str | None:
    if isinstance(value, str):
        return value or None
    if isinstance(value, dict):
        return value.get("text") or value.get("term")
    return None


def options_literal(options: list[dict[str, Any]]) -> str:
    if not isinstance(options, list):
        raise ValueError("typed_options_required")
    names = [item["name"] for item in options]
    if len(names) != len(set(names)):
        raise ValueError("duplicate_option")
    rows = []
    for setting in sorted(options, key=lambda item: item["name"]):
        kind, value = setting["type"], setting["value"]
        if kind == "bool" and isinstance(value, bool):
            literal = "true" if value else "false"
        elif kind in {"nat", "int"} and isinstance(value, int) and not isinstance(value, bool) and (kind == "int" or value >= 0):
            literal = str(value) if value >= 0 else f"({value})"
        elif kind == "string" and isinstance(value, str):
            literal = _string(value)
        elif kind == "name" and isinstance(value, str):
            literal = _quoted_name(value)
        else:
            raise ValueError("unsupported_option_type:" + str(kind))
        rows.append(f"{{ name := {_quoted_name(setting['name'])}, value := .{kind} {literal} }}")
    return "#[" + ", ".join(rows) + "]"


def _term(value: Any) -> str:
    term = _expression(value)
    if not term:
        raise ValueError("missing_mathematical_term")
    return "(" + term + ")"


def _ref(value: Any) -> str:
    return "⟨" + _term(value) + "⟩"


def _option(value: Any, ref: bool = False) -> str:
    if not _expression(value):
        return "none"
    return "some " + (_ref(value) if ref else _term(value))


def _array(values: list[Any], render) -> str:
    return "#[" + ", ".join(render(value) for value in values) + "]"


def _selection(selection: dict[str, Any] | None) -> str:
    if selection is None:
        return "none"
    definition = selection.get("definition")
    if definition is None:
        definition_literal = "none"
    else:
        definition_literal = "some { owner := " + _quoted_name(definition["owner"]) + ", name := " + _quoted_name(definition["name"]) + ", path := " + _array(definition["path"], _string) + " }"
    readouts = []
    for readout in selection["readouts"]:
        operand = readout.get("stateOperand")
        readouts.append("{ path := " + _array(readout["path"], _string) +
                        ", stateBinder := " + str(readout["stateBinder"]) +
                        ", functionOperand := " + ("true" if readout.get("functionOperand", False) else "false") +
                        ", stateOperand := " + ("none" if operand is None else "some " + _array(operand, _string)) +
                        ", booleanPredicate := " + ("true" if readout.get("booleanPredicate", False) else "false") + " }")
    return "some { owner := " + _quoted_name(selection["owner"]) + ", definition := " + definition_literal + ", coordinates := " + _array(selection["coordinates"], str) + ", readouts := #[" + ", ".join(readouts) + "] }"


def _levels(row: dict[str, Any]) -> list[str]:
    return list(row.get("level_params", []))


def _suffix(levels: list[str]) -> str:
    return ".{" + ", ".join(levels) + "}" if levels else ""


def _constant(name: str, levels: list[str] | None = None) -> str:
    return "@_root_." + _name(name) + _suffix(levels or [])


def _continuation(reg: Registration) -> str:
    if reg.continuation == "open":
        return ".unknown"
    if reg.continuation:
        return ".evidence " + _ref(reg.continuation)
    return ".absent"


def _bridge(reg: Registration, index: int) -> str:
    row = reg.snapshot or {}
    kind = row.get("bridge_kind", "source" if reg.source and not reg.finite_source else "legacy")
    arena = _term(reg.arena if row.get("bridge_arena_from_source", False) else (row.get("bridge_arena") or reg.arena))
    if kind == "source":
        return f".source {arena} {_ref(reg.source_record or reg.realization)}"
    actual = _expression(getattr(reg, "actual", None)) or _expression(row.get("actual") or row.get("realization_actual"))
    if reg.inline_bridge:
        actual = reg.inline_bridge[0]
    if reg.native:
        actual = reg.primitive
        primitives = f"({_term(actual)}).toPrimitiveBundle"
        bridge = f"Iff.rfl"
    else:
        primitives = _term(reg.primitive)
        bridge = reg.finite_bridge or reg.realization
    if reg.inline_bridge:
        bridge = f"__p2b_inline_bridge_{index + 1}"
    if kind not in {"legacy", "forward", "witness"}:
        raise ValueError("unknown_bridge_kind:" + str(kind))
    result = f".{kind} {arena} {_term(actual)} {primitives} {_ref(bridge)}"
    if kind == "witness":
        result += f" (And.left {_term(reg.variation)})"
    return result


def _registration_type(reg: Registration, row: dict[str, Any]) -> str:
    levels = _levels(row)
    universes = row.get("registration_universes")
    arguments = row.get("type_args")
    if universes is None or arguments is None:
        # Missing elaboration metadata is rejected by the planner for retained
        # output. A renderer probe may use inference without claiming a build.
        universes = ["_"] * 8 + ["0", "0", "0"] + ["_"] * 5 + ["0"]
        arguments = ["_", "_", "_" if reg.readout else "Unit", "_" if reg.variation else "Unit",
                     "_" if reg.sensitivity else "Unit", "_" if reg.escape_from else "Unit",
                     "_" if reg.continuation and reg.continuation != "open" else "Unit",
                     "_" if reg.source_record and not reg.source else "Unit"]
    return "Contract.Registration" + _suffix(universes) + " (" + _constant(reg.theorem, levels) + ") " + " ".join(_term(arg) for arg in arguments)


def render_registration(reg: Registration, index: int = 0) -> str:
    row = reg.snapshot or {}
    levels = _levels(row)
    source = row.get("realization_source")
    realization_source = "some " + _quoted_name(source) if source else "none"
    lines = [
        f"noncomputable def registration_{index + 1}{_suffix(levels)} : {_registration_type(reg, row)} := {{",
        f"  unitName := {_quoted_name(row.get('unit', reg.theorem + '.__information_unit'))},",
        f"  realizationName := {_quoted_name(row.get('realization', reg.realization or reg.source_record or reg.theorem))},",
        f"  realizationSource := {realization_source},",
        f"  generated := {'true' if row.get('generated', reg.native) else 'false'},",
        f"  arena := {_ref(reg.arena or row.get('arena_term'))},",
        f"  objectArena := {_ref(reg.object_arena or reg.arena or row.get('object_arena_term'))},",
        f"  catalog := {_quoted_name(row.get('catalog', reg.catalog or reg.arena))},",
        f"  localNames := {'true' if row.get('local_registration_names', not (reg.source or reg.occurrence)) else 'false'},",
        f"  realization := {_bridge(reg, index)},",
        f"  readout := {_option(reg.readout)},",
        f"  variation := {_option(reg.variation, True)},",
        f"  sensitivity := {_option(reg.sensitivity, True)},",
        f"  escapeFrom := {_option(reg.escape_from)},",
        f"  sourceSelection := {_selection(row.get('source_selection'))},",
        f"  continuation := {_continuation(reg)},",
        f"  familyRecord := {_option(reg.source_record if not reg.source or reg.finite_source else None, True)},",
        f"  options := {options_literal(reg.options)} }}",
    ]
    if reg.inline_bridge:
        actual, proof = reg.inline_bridge
        bridge_type = row.get("inline_bridge_type") or (
            "D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization " +
            _term(reg.arena) + " (" + _constant(reg.theorem, levels) + ") " + _term(actual))
        lines[:0] = [f"theorem __p2b_inline_bridge_{index + 1}{_suffix(levels)} : {bridge_type} := {proof}", ""]
    if reg.native:
        if not getattr(reg, "statement", None) or not getattr(reg, "proof", None):
            raise ValueError("missing_native_theorem")
        lines[:0] = [f"theorem _root_.{_name(reg.theorem)}{_suffix(levels)} : {reg.statement} := {reg.proof}", ""]
    return "\n".join(lines) + "\n"


def _occurrence_rows(rows: list[dict[str, Any]]) -> str:
    rendered = []
    for row in rows:
        theorem = row["theorem"]
        statement = _expression(row.get("captured_statement")) or row.get("statement") or "_"
        proof = _expression(row.get("proof")) or _constant(theorem, row.get("level_params", []))
        identity = row.get("statement_identity", "")
        rendered.append("{ statement := " + _term(statement) + ", proof := " + _term(proof) +
                        ", theoremName := " + _quoted_name(theorem) + ", objectArenaName := " +
                        _quoted_name(row["object_arena"]) + ", statementIdentity := " +
                        ("some " + _string(identity) if identity else "none") +
                        ", registrationModuleName := " + _quoted_name(row["registration_module"]) + " }")
    return "#[" + ",\n    ".join(rendered) + "]"


def render_root(root: Root, kind: str, destination_module: str) -> str:
    ignored = {"LeanInformationAuditInterface.Syntax", "LeanInformationAuditInterface.Store", "LeanInformationAuditInterface.RootContract"}
    imports = ["import LeanInformationAuditInterface.Contract.Catalog"] + [
        "import " + item for item in sorted(set(root.imports)) if item not in ignored]
    levels = sorted({level for rows in [root.expected, root.source, root.baseline] for row in rows for level in row.get("level_params", [])})
    lines = [*imports, "", f"namespace {destination_module}", "open LeanInformationAudit", "",
             f"def rootCatalog{_suffix(levels)} : Contract.RootCatalog := {{ data := {{",
             f"  rootId := {_quoted_name(destination_module)},",
             f"  expected := {_occurrence_rows(root.expected)},",
             f"  source := {_occurrence_rows(root.source)},",
             f"  baseline := {_occurrence_rows(root.baseline)},",
             f"  companionPrefix := {'some ' + _quoted_name(root.companion_prefix) if root.companion_prefix else 'none'} }} }}"]
    if kind == "sealed_catalog":
        lines += ["", f"def seal : Contract.Seal := {{ rootId := {_quoted_name(destination_module)}, options := {options_literal(getattr(root, 'seal_options', []))} }}"]
    lines += ["", f"end {destination_module}"]
    return "\n".join(lines) + "\n"


def render_template(template: Template, index: int) -> str:
    row = getattr(template, "snapshot", None) or {}
    levels = row.get("level_params", [])
    constructor_types = row.get("constructor_types", {})
    if isinstance(constructor_types, list):
        constructor_types = {item["name"]: item["type"] for item in constructor_types}
    constructors = "#[" + ", ".join("{ name := " + _quoted_name(name) + ", type := " + _term(constructor_types.get(name, name)) + " }" for name in template.constructors) + "]"
    universes = row.get("enrollment_universes", ["_", "0"])
    return (f"noncomputable def enrollment_{index + 1}{_suffix(levels)} : Contract.TemplateEnrollment{_suffix(universes)} ({_constant(template.name, levels)}) := {{\n"
            f"  name := {_quoted_name(template.name)}, version := {template.version}, constructors := {constructors},\n"
            f"  options := {options_literal(template.options)} }}\n")


def render_seal(seal: Seal, destination_module: str) -> str:
    return ("import LeanInformationAuditInterface.Contract.Catalog\n\n" +
            f"namespace {destination_module}\n" +
            f"def seal : LeanInformationAudit.Contract.Seal := {{ rootId := {_quoted_name(destination_module)}, options := {options_literal(seal.options)} }}\n" +
            f"end {destination_module}\n")


def replace_spans(text: str, replacements: list[tuple[int, int, str]]) -> str:
    raw = text.encode("utf-8")
    previous = len(raw)
    for start, end, replacement in sorted(replacements, reverse=True):
        if not 0 <= start <= end <= previous:
            raise ValueError("overlapping_or_invalid_span")
        # Decode both boundaries to reject an offset inside a UTF-8 character.
        raw[:start].decode("utf-8")
        raw[:end].decode("utf-8")
        raw = raw[:start] + replacement.encode("utf-8") + raw[end:]
        previous = start
    return raw.decode("utf-8")
