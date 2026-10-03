from __future__ import annotations

import json
from typing import Any

from .model import Registration, Root, Seal, Template
from .snapshot import SnapshotError, closed_printed_term, type_arg_source_slots


def _name(value: str) -> str:
    return value.removeprefix("_root_.")


def _name_components(value: Any) -> list[str | int] | None:
    if value is None:
        return None
    if not isinstance(value, list) or any(not isinstance(item, str) and type(item) is not int for item in value):
        raise SnapshotError("invalid_name_components", repr(value))
    if any(type(item) is int and item < 0 for item in value):
        raise SnapshotError("invalid_name_components", repr(value))
    return value


def _quoted_name(value: str, components: Any = None) -> str:
    components = _name_components(components)
    if components is not None:
        if not components:
            return "Lean.Name.anonymous"
        if any(type(item) is int or isinstance(item, str) and not item.isidentifier() for item in components) or components[0] == "_private":
            result = "Lean.Name.anonymous"
            for item in components:
                if type(item) is int:
                    result = f"(Lean.Name.num {result} {item})"
                else:
                    result = f"(Lean.Name.str {result} {_string(item)})"
            return result
        return "`" + ".".join(components)
    elif _name(value).startswith("_private."):
        raise SnapshotError("missing_name_components", value)
    return "`" + _name(value) if value else "Lean.Name.anonymous"


def _row_name(row: dict[str, Any], field: str, fallback: str = "") -> str:
    components = row.get("name_components", {})
    if not isinstance(components, dict):
        raise SnapshotError("invalid_name_components", field)
    return _quoted_name(str(row.get(field, fallback)), components.get(field))


def _private_name(value: str, components: Any = None) -> bool:
    components = _name_components(components)
    return _name(value).startswith("_private.") or bool(components and any(type(item) is int or isinstance(item, str) and "»" in item for item in components))


def target_uses_controlled_printing(row: dict[str, Any], field: str = "theorem") -> bool:
    components = row.get("name_components", {})
    if not isinstance(components, dict):
        raise SnapshotError("invalid_name_components", field)
    return _private_name(str(row.get(field, "")), components.get(field))


def _target(row: dict[str, Any], name: str, levels: list[str], field: str = "theorem") -> str:
    components = row.get("name_components", {})
    if not isinstance(components, dict):
        raise SnapshotError("invalid_name_components", field)
    if _private_name(name, components.get(field)):
        if components.get(field) is None:
            raise SnapshotError("missing_name_components", name)
        target_field = "target_term" if field == "theorem" else "template_term"
        term = closed_printed_term(row.get(target_field), target_field)
        if field == "name" and not term:
            source = row.get("parser_slots", {}).get("name")
            if source:
                specialized = bool(row.get("source_specializations", {}).get("name"))
                return "@" + source + ("" if specialized else _suffix(levels))
        if not term:
            raise SnapshotError("missing_private_target_term", name)
        return term
    return _constant(name, levels, components.get(field))


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
            literal = _quoted_name(value, setting.get("value_components"))
        else:
            raise ValueError("unsupported_option_type:" + str(kind))
        rows.append(f"{{ name := {_quoted_name(setting['name'], setting.get('name_components'))}, value := .{kind} {literal} }}")
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
        definition_literal = "some { owner := " + _row_name(definition, "owner") + ", name := " + _row_name(definition, "name") + ", path := " + _array(definition["path"], _string) + " }"
    readouts = []
    for readout in selection["readouts"]:
        operand = readout.get("stateOperand")
        readouts.append("{ path := " + _array(readout["path"], _string) +
                        ", stateBinder := " + str(readout["stateBinder"]) +
                        ", functionOperand := " + ("true" if readout.get("functionOperand", False) else "false") +
                        ", stateOperand := " + ("none" if operand is None else "some " + _array(operand, _string)) +
                        ", booleanPredicate := " + ("true" if readout.get("booleanPredicate", False) else "false") + " }")
    return "some { owner := " + _row_name(selection, "owner") + ", definition := " + definition_literal + ", coordinates := " + _array(selection["coordinates"], str) + ", readouts := #[" + ", ".join(readouts) + "] }"


def _levels(row: dict[str, Any]) -> list[str]:
    return list(row.get("level_params", []))


def _suffix(levels: list[str]) -> str:
    return ".{" + ", ".join(levels) + "}" if levels else ""


def _constant(name: str, levels: list[str] | None = None, components: Any = None) -> str:
    components = _name_components(components)
    if components is not None:
        if any(type(item) is int for item in components):
            raise SnapshotError("missing_private_target_term", name)
        name = ".".join(item if item.isidentifier() else "«" + item + "»" for item in components)
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
    if row.get("bridge_arena_from_source") is False and row.get("bridge_arena") is None:
        raise SnapshotError("missing_material", "compiled normalized bridge arena")
    arena = _term(reg.arena if row.get("bridge_arena_from_source", False) else (row.get("bridge_arena") or reg.arena))
    if kind == "source":
        return f".source {arena} {_ref(reg.source_record or reg.realization)}"
    actual = _expression(getattr(reg, "actual", None)) or _expression(row.get("actual") or row.get("realization_actual"))
    if reg.inline_bridge:
        actual = reg.inline_bridge[0]
    if reg.native:
        actual = reg.primitive
        primitives = f"({_term(actual)}).toPrimitiveBundle"
        bridge = "⟨Iff.rfl⟩"
    else:
        primitives = _term(reg.primitive)
        bridge = reg.finite_bridge or reg.realization or reg.via_descriptor
    if reg.inline_bridge:
        bridge = row.get("inline_bridge_term") or (_constant(row["realization"], _levels(row) + row.get("extra_level_params", [])) if row.get("realization") else f"__p2b_inline_bridge_{index + 1}")
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
    sources = type_arg_source_slots(row)
    rendered_arguments = ["(type_of% (" + row["parser_slots"][source] + "))" if source is not None else _term(arg)
                          for source, arg in zip(sources, arguments)]
    return "LeanInformationAudit.Contract.Registration" + _suffix(universes) + " (" + _target(row, reg.theorem, levels) + ") " + " ".join(rendered_arguments)


def generated_declaration_name(row: dict[str, Any], name: str) -> tuple[str, str]:
    namespace = row.get("namespace", "")
    if namespace:
        return name, namespace + "." + name
    owner = row.get("owner", "")
    return ("_root_." + owner + "." + name, owner + "." + name) if owner else (name, name)


def _declaration_levels(row: dict[str, Any], levels: list[str]) -> list[str]:
    return [level for level in levels if level not in row.get("ambient_universes", [])]


def _scoped_commands(row: dict[str, Any], commands: list[str]) -> str:
    prefix = row.get("scope_prefix", "")
    return ("\n\n" + prefix).join(commands) + "\n"


def render_registration(reg: Registration, index: int = 0) -> str:
    row = reg.snapshot or {}
    levels = _levels(row)
    declaration_levels = _declaration_levels(row, levels + [level for level in row.get("extra_level_params", []) if level not in levels])
    source = row.get("realization_source")
    realization_source = "some " + _row_name(row, "realization_source") if source else "none"
    declaration_name, _ = generated_declaration_name(row, f"registration_{index + 1}")
    lines = [
        f"noncomputable def {declaration_name}{_suffix(declaration_levels)} : {_registration_type(reg, row)} := {{",
        f"  unitName := {_row_name(row, 'unit', reg.theorem + '.__information_unit')},",
        f"  realizationName := {_row_name(row, 'realization', reg.realization or reg.source_record or reg.theorem)},",
        f"  realizationSource := {realization_source},",
        f"  generated := {'true' if row.get('generated', reg.native) else 'false'},",
        f"  arena := {_ref(reg.arena or row.get('arena_term'))},",
        f"  objectArena := {_ref(reg.object_arena or reg.arena or row.get('object_arena_term'))},",
        f"  catalog := {_row_name(row, 'catalog', reg.catalog or reg.arena)},",
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
    commands = []
    if reg.native:
        if not getattr(reg, "statement", None) or not getattr(reg, "proof", None):
            raise ValueError("missing_native_theorem")
        commands.append(f"theorem _root_.{_name(reg.theorem)}{_suffix(_declaration_levels(row, levels))} : {reg.statement} := {reg.proof}")
    if reg.inline_bridge:
        actual, proof = reg.inline_bridge
        bridge_type = row.get("inline_bridge_type") or row.get("bridge_type") or (
            "D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization " +
            _term(reg.arena) + " (" + _target(row, reg.theorem, levels) + ") " + _term(actual))
        bridge_type = _expression(bridge_type)
        bridge_name = "_root_." + _name(row["realization"]) if row.get("realization") else f"__p2b_inline_bridge_{index + 1}"
        bridge_levels = _declaration_levels(row, row.get("inline_bridge_level_params", declaration_levels))
        commands.append(f"theorem {bridge_name}{_suffix(bridge_levels)} : {bridge_type} := {proof}")
    helpers = row.get("companion_helpers", [])
    if helpers:
        for helper in helpers:
            helper_levels = _declaration_levels(row, helper.get("level_params", []))
            commands.append(f"noncomputable def {helper['name']}{_suffix(helper_levels)} : {_expression(helper['type'])} := {_expression(helper['body'])}")
    commands.append("\n".join(lines))
    return _scoped_commands(row, commands)


def _occurrence_rows(rows: list[dict[str, Any]]) -> str:
    rendered = []
    for row in rows:
        theorem = row["theorem"]
        statement = _expression(row.get("captured_statement")) or row.get("statement") or "_"
        proof = _expression(row.get("proof")) or _target(row, theorem, row.get("level_params", []))
        identity = row.get("statement_identity", "")
        rendered.append("{ statement := " + _term(statement) + ", proof := " + _term(proof) +
                        ", theoremName := " + _row_name(row, "theorem") + ", objectArenaName := " +
                        _row_name(row, "object_arena") + ", statementIdentity := " +
                        ("some " + _string(identity) if identity else "none") +
                        ", registrationModuleName := " + _row_name(row, "registration_module") + " }")
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
             f"  companionPrefix := {'some ' + _row_name(root.snapshot or {}, 'companion_prefix', root.companion_prefix) if root.companion_prefix else 'none'} }} }}"]
    if kind == "sealed_catalog":
        lines += ["", f"def «seal» : Contract.Seal := {{ rootId := {_quoted_name(destination_module)}, options := {options_literal(getattr(root, 'seal_options', []))} }}"]
    lines += ["", f"end {destination_module}"]
    return "\n".join(lines) + "\n"


def render_template(template: Template, index: int) -> str:
    row = getattr(template, "snapshot", None) or {}
    levels = row.get("level_params", [])
    declaration_levels = _declaration_levels(row, levels + row.get("extra_level_params", []))
    constructor_types = row.get("constructor_types", {})
    if isinstance(constructor_types, list):
        constructor_types = {item["name"]: item["type"] for item in constructor_types}
    constructors = "#[" + ", ".join("{ name := " + _quoted_name(name, row.get("constructor_name_components", {}).get(name)) + ", type := " + _term(constructor_types.get(name, name)) + " }" for name in template.constructors) + "]"
    universes = row.get("enrollment_universes", ["_", "0"])
    declaration_name, _ = generated_declaration_name(row, f"enrollment_{index + 1}")
    return _scoped_commands(row, [f"noncomputable def {declaration_name}{_suffix(declaration_levels)} : LeanInformationAudit.Contract.TemplateEnrollment{_suffix(universes)} ({_target(row, template.name, levels, "name")}) := {{\n"
            f"  name := {_row_name(row, 'name', template.name)}, version := {template.version}, constructors := {constructors},\n"
            f"  options := {options_literal(template.options)} }}"])


def render_seal(seal: Seal, destination_module: str) -> str:
    return ("import LeanInformationAuditInterface.Contract.Catalog\n\n" +
            f"namespace {destination_module}\n" +
            f"def «seal» : LeanInformationAudit.Contract.Seal := {{ rootId := {_quoted_name(destination_module)}, options := {options_literal(seal.options)} }}\n" +
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
