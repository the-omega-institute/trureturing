from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .lean_syntax import (byte_slice, load_syntax_snapshot, parse_repository, relative_reg_path,
                          source_module, syntax_sources)
from .model import Failure, GeneratedFile, PlanResult, Registration, Root, Seal, Template
from .render import generated_declaration_name, render_registration, render_root, render_template, replace_spans, target_uses_controlled_printing
from .snapshot import SnapshotError, closed_printed_term, load_input_snapshot, sha256_file, type_arg_source_slots, typed_options, validate_expression_levels, validate_level_params, validate_universe_text


class GeneratorFailure(RuntimeError):
    pass


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Generator:
    def __init__(self, repo: Path, inputs: Path, mapping: Path | None = None, syntax: Path | None = None):
        self.repo = repo.resolve()
        self.inputs_path = inputs.resolve()
        self.mapping_path = mapping.resolve() if mapping else None
        self.syntax_path = syntax.resolve() if syntax else None

    def plan(self, expected_sha256: str | None = None) -> PlanResult:
        try:
            return self._plan(expected_sha256)
        except SnapshotError as error:
            return PlanResult("", [], [], [], [], [], [Failure(error.code, error.path, error.detail)], {"reconciliation": []})
        except (OSError, ValueError, KeyError, TypeError) as error:
            return PlanResult("", [], [], [], [], [], [Failure("invalid_snapshot", str(self.inputs_path), str(error))], {"reconciliation": []})

    def _plan(self, expected_sha256: str | None) -> PlanResult:
        snapshot, input_sha = load_input_snapshot(self.inputs_path)
        if expected_sha256 and expected_sha256 != input_sha:
            raise SnapshotError("snapshot_sha_mismatch", f"expected {expected_sha256}, got {input_sha}", str(self.inputs_path))
        syntax = load_syntax_snapshot(self.syntax_path, snapshot)
        originals = syntax_sources(syntax)
        registrations, templates, roots, seals, notations = parse_repository(self.repo, syntax)
        failures: list[Failure] = []

        def fail(code: str, detail: str, path: str = "") -> None:
            failures.append(Failure(code, path, detail))

        # Captured module source bytes bind compiled entries and their Options.
        # Roots and seals have no sourceText in Store and need a compile manifest.
        bound_sources: dict[str, str] = {}
        for category in ("registrations", "templates"):
            for row in snapshot[category]:
                owner = row.get("owner")
                if not isinstance(owner, str) or not owner:
                    fail("missing_input_owner", category)
                    continue
                relative = owner.replace(".", "/") + ".lean"
                source = row.get("source_text")
                if relative in originals and source == originals[relative]:
                    previous = bound_sources.setdefault(relative, source)
                    if previous != source:
                        fail("compiled_source_conflict", owner)
        manifest = snapshot.get("compiled_sources", [])
        if not isinstance(manifest, list):
            fail("invalid_compile_manifest", "compiled_sources must be an array")
            manifest = []
        manifest_seen: set[str] = set()
        for item in manifest:
            relative = relative_reg_path(item.get("path"))
            if relative in manifest_seen:
                fail("duplicate_compile_source", relative)
            manifest_seen.add(relative)
            if relative not in originals:
                fail("extra_compile_source", relative)
                continue
            if item.get("trace_verified") is False:
                fail("unverified_compile_source", relative)
            source = item.get("source_text")
            digest = item.get("source_sha256")
            if source is not None and source != originals[relative]:
                fail("compiled_source_mismatch", relative)
            elif digest is not None and digest != _sha256_text(originals[relative]):
                fail("compiled_source_mismatch", relative)
            elif source is None and digest is None:
                fail("missing_compile_source_binding", relative)
            else:
                bound_sources[relative] = originals[relative]

        def bind(items: list[Any], category: str, source_required: bool) -> None:
            by_owner: dict[str, list[Any]] = defaultdict(list)
            for item in items:
                relative = item.path.relative_to(self.repo).as_posix()
                by_owner[source_module(relative)].append(item)
            rows_by_owner: dict[str, list[dict[str, Any]]] = defaultdict(list)
            for row in snapshot[category]:
                owner = row.get("owner")
                if not isinstance(owner, str) or not owner:
                    fail("missing_input_owner", category)
                    continue
                rows_by_owner[owner].append(row)
            for owner in sorted(set(by_owner) | set(rows_by_owner)):
                source_items = sorted(by_owner.get(owner, []), key=lambda item: item.span.start)
                raw_rows = rows_by_owner.get(owner, [])
                seen: set[int] = set()
                relative = owner.replace(".", "/") + ".lean"
                original = originals.get(relative)
                for row in raw_rows:
                    index = row.get("source_index")
                    captured = row.get("source_text")
                    if index is not None:
                        if type(index) is not int or not 0 <= index < len(source_items):
                            fail("extra_compiled_input", f"{category}:{owner}:{index}", str(self.inputs_path))
                            continue
                        candidates = [index]
                    elif len(source_items) == 1:
                        candidates = [0]
                    else:
                        fail("missing_source_index", f"{category}:{owner}")
                        continue
                    if not candidates:
                        fail("compiled_source_mismatch" if source_items else "extra_compiled_input", f"{category}:{owner}")
                        continue
                    if len(candidates) != 1:
                        fail("ambiguous_compiled_input", f"{category}:{owner}")
                        continue
                    position = candidates[0]
                    if position in seen:
                        fail("duplicate", f"{category}:{owner}:{position}")
                        continue
                    item = source_items[position]
                    if source_required and captured != original:
                        fail("compiled_source_mismatch", f"{category}:{owner}:{position}")
                        continue
                    if not source_required and relative not in bound_sources:
                        # Synthetic snapshots may provide source_text directly.
                        if captured == original:
                            bound_sources[relative] = original
                        else:
                            fail("missing_compile_source_binding", f"{category}:{owner}")
                            continue
                    seen.add(position)
                    parser_metadata = item.snapshot or {}
                    item.snapshot = {**row, **parser_metadata, "source_index": position}
                    if category != "roots":
                        try:
                            item.options = typed_options(row.get("options"))
                        except SnapshotError as error:
                            fail(error.code, f"{category}:{owner}:{error.detail}")
                for position in sorted(set(range(len(source_items))) - seen):
                    fail("missing_compiled_input", f"{category}:{owner}:{position}", relative)

        bind(registrations, "registrations", True)
        bind(templates, "templates", True)
        bind(roots, "roots", False)
        bind(seals, "seals", False)
        specialization_audit: list[dict[str, Any]] = []
        for category, items in (("registrations", registrations), ("templates", templates)):
            for item in items:
                row = item.snapshot or {}
                if "owner" not in row:
                    continue
                specializations = row.get("source_specializations", {})
                if not isinstance(specializations, dict):
                    fail("invalid_source_specializations", row["owner"], str(item.path))
                    continue
                slots = row["parser_slots"]
                declared_levels = row.get("level_params", []) + row.get("extra_level_params", []) if isinstance(row.get("level_params", []), list) and isinstance(row.get("extra_level_params", []), list) else []
                for slot, entries in sorted(specializations.items()):
                    span = row["parser_slot_spans"].get(slot)
                    identifiers = row["parser_slot_identifiers"].get(slot, [])
                    if span is None or not isinstance(entries, list):
                        fail("invalid_source_specializations", f"{row['owner']}:{slot}")
                        continue
                    edits: list[tuple[int, int, str]] = []
                    accepted = []
                    universe_mapping: dict[str, str] = {}
                    for entry in entries:
                        if not isinstance(entry, dict):
                            fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                            continue
                        start, end, text, term = (entry.get(key) for key in ("start", "end", "text", "term"))
                        kind = entry.get("kind", "constant")
                        if kind not in {"constant", "universe-parameter"}:
                            fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                            continue
                        occurrences = row["parser_slot_universes"].get(slot, []) if kind == "universe-parameter" else identifiers
                        matches = [identifier for identifier in occurrences if
                                   (identifier.get("start"), identifier.get("end"), identifier.get("text")) == (start, end, text)]
                        if type(start) is not int or type(end) is not int or not span["start"] <= start < end <= span["end"] or len(matches) != 1:
                            fail("source_specialization_span_mismatch", f"{row['owner']}:{slot}")
                            continue
                        levels = entry.get("levels")
                        if not isinstance(levels, list) or any(not isinstance(level, str) or not level for level in levels):
                            fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                            continue
                        if kind == "universe-parameter":
                            if len(levels) != 1:
                                fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                                continue
                            components = matches[0].get("name_components")
                            if not isinstance(components, list) or not components or any(not isinstance(component, str) and type(component) is not int or type(component) is int and component < 0 for component in components):
                                fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                                continue
                            key = json.dumps(components, ensure_ascii=False)
                            if key in universe_mapping and universe_mapping[key] != levels[0]:
                                fail("ambiguous_source_universe_mapping", f"{row['owner']}:{slot}")
                                continue
                            universe_mapping[key] = levels[0]
                            expected = {levels[0], "(" + levels[0] + ")"}
                        else:
                            head = matches[0].get("head_text")
                            if not isinstance(head, str) or not head:
                                fail("invalid_source_specialization", f"{row['owner']}:{slot}")
                                continue
                            expected = {head + (".{" + ", ".join(levels) + "}" if levels else "")}
                        if not isinstance(term, str) or term not in expected or byte_slice(originals[item.path.relative_to(self.repo).as_posix()], start, end, slot) != text:
                            fail("source_specialization_term_mismatch", f"{row['owner']}:{slot}")
                            continue
                        try:
                            controlled = {"text": term, "printed": True, "level_params": entry.get("level_params", [])}
                            closed_printed_term(controlled, "source_specializations:" + slot)
                            for level in levels:
                                validate_universe_text(level, "source_specializations:" + slot)
                            validate_expression_levels(controlled, declared_levels, "source_specializations:" + slot)
                        except SnapshotError as error:
                            fail(error.code, f"{row['owner']}:{slot}")
                            continue
                        edits.append((start - span["start"], end - span["start"], term))
                        accepted.append(entry)
                    try:
                        slots[slot] = replace_spans(slots[slot], edits)
                    except ValueError:
                        fail("overlapping_source_specializations", f"{row['owner']}:{slot}")
                    if accepted:
                        specialization_audit.append({"category": category, "owner": row["owner"],
                                                     "source_index": row["source_index"], "slot": slot,
                                                     "entries": sorted(accepted, key=lambda entry: (entry["start"], entry["end"]))})
                if category == "registrations":
                    for field in ("arena", "object_arena", "catalog", "primitive", "realization", "variation", "sensitivity", "readout", "output_evidence", "escape_from", "escape_from_source", "continuation", "source_record", "finite_bridge", "via_descriptor"):
                        if field in slots:
                            setattr(item, field, slots[field])
                    if "inline_actual" in slots and "inline_proof" in slots:
                        item.inline_bridge = (slots["inline_actual"], slots["inline_proof"])
                    item.statement, item.proof = slots.get("target_type"), slots.get("native_proof")
        compile_blockers: list[dict[str, Any]] = []
        for reg in registrations:
            row = reg.snapshot or {}
            if "owner" not in row:
                continue
            if row.get("source_target_matches") is False:
                compile_blockers.append({"code": "source_target_contract_mismatch", "owner": row["owner"],
                                         "source_index": row.get("source_index"), "theorem": row.get("theorem"),
                                         "theorem_type": row.get("theorem_type"), "bridge_type": row.get("bridge_type")})
            if row.get("registration_module", row["owner"]) != row["owner"]:
                fail("wrong_registration_owner", str(row.get("registration_module")), str(reg.path))
            if row.get("bridge_arena_from_source") is False and row.get("bridge_arena") is None:
                fail("missing_material", "compiled normalized bridge arena", str(reg.path))
            try:
                validate_level_params(row, reg.module_name)
            except SnapshotError as error:
                fail(error.code, error.detail, str(reg.path))
                continue
            declared_levels = row.get("level_params", []) + row.get("extra_level_params", []) if isinstance(row.get("level_params", []), list) and isinstance(row.get("extra_level_params", []), list) else []
            theorem = row.get("theorem")
            if not isinstance(theorem, str) or not theorem:
                fail("missing_material", "compiled theorem name", str(reg.path))
            else:
                reg.theorem = theorem
            universes, arguments = row.get("registration_universes"), row.get("type_args")
            if not isinstance(universes, list) or len(universes) != 17 or not isinstance(arguments, list) or len(arguments) != 8:
                fail("missing_material", "registration universe/type arguments", str(reg.path))
            else:
                for index, universe in enumerate(universes):
                    try:
                        validate_universe_text(universe, f"registration_universes[{index}]")
                    except SnapshotError as error:
                        fail(error.code, f"{reg.module_name}:{error.detail}", str(reg.path))
                try:
                    type_sources = type_arg_source_slots(row)
                except SnapshotError as error:
                    fail(error.code, f"{reg.module_name}:{error.detail}", str(reg.path))
                    type_sources = [None] * 8
                for index, value in enumerate(arguments):
                    if type_sources[index] is not None:
                        continue
                    try:
                        if closed_printed_term(value, f"type_args[{index}]") is None:
                            raise SnapshotError("missing_type_arg_source", f"type_args[{index}]")
                        validate_expression_levels(value, declared_levels, f"type_args[{index}]")
                        reg.controlled_printing.append(f"type_args[{index}]")
                    except SnapshotError as error:
                        fail(error.code, f"{reg.module_name}:type_args[{index}]", str(reg.path))
            reg.catalog = row.get("catalog", reg.catalog)
            reg.native = reg.variant == "native"
            slots = row.get("parser_slots", {})
            if row.get("open_continuation") and not reg.continuation:
                reg.continuation = "open"
            for field in ("bridge_arena", "inline_bridge_type", "inline_bridge_term", "target_term"):
                if field == "target_term":
                    if not target_uses_controlled_printing(row):
                        continue
                if field == "bridge_arena" and row.get("bridge_arena_from_source"):
                    continue
                if row.get(field) is not None:
                    try:
                        closed_printed_term(row[field], field)
                        field_levels = row.get("inline_bridge_level_params", declared_levels) if field == "inline_bridge_type" else declared_levels
                        validate_expression_levels(row[field], field_levels, field)
                        reg.controlled_printing.append(field)
                    except SnapshotError as error:
                        fail(error.code, f"{reg.module_name}:{field}", str(reg.path))
            if reg.inline_bridge:
                try:
                    validate_level_params({"level_params": row.get("inline_bridge_level_params", row.get("level_params", []))}, reg.module_name + ":inline")
                except SnapshotError as error:
                    fail(error.code, error.detail, str(reg.path))
                reg.actual = reg.inline_bridge[0]
            elif reg.native and reg.primitive:
                reg.actual = reg.primitive
            if not reg.object_arena and row.get("object_arena") in {None, "", row.get("arena")}:
                reg.object_arena = reg.arena
            if reg.finite_source and reg.finite_bridge:
                reg.realization = reg.finite_bridge
            for attribute, field in (("primitive", "supplied_primitives"), ("readout", "readout"),
                                     ("via_descriptor", "via_descriptor"), ("output_evidence", "output_evidence"),
                                     ("actual", "actual"), ("escape_from_source", "source_selection"),
                                     ("escape_from", "escape_from"), ("continuation", "continuation"),
                                     ("arena", "arena_term"), ("object_arena", "object_arena_term"),
                                     ("realization", "realization_term"), ("variation", "variation_term"),
                                     ("sensitivity", "sensitivity_term")):
                if getattr(reg, attribute, None) is not None or field not in row or row[field] is None:
                    continue
                try:
                    value = closed_printed_term(row[field], field)
                    validate_expression_levels(row[field], declared_levels, field)
                    setattr(reg, attribute, value)
                    reg.controlled_printing.append(field)
                except SnapshotError as error:
                    fail(error.code, f"{reg.module_name}:{field}", str(reg.path))
            if reg.finite_source and reg.finite_bridge:
                reg.realization = reg.finite_bridge
            if not reg.arena:
                fail("missing_material", "arena", str(reg.path))
            if reg.source and not reg.source_record:
                reg.source_record = slots.get("source_record") or reg.realization
            if reg.variant in {"legacy", "witness", "forward"} and not reg.realization and not reg.inline_bridge and not reg.via_descriptor:
                fail("missing_material", "realization", str(reg.path))
            if reg.variant in {"legacy", "witness", "forward"} and not reg.primitive:
                fail("missing_material", "primitives", str(reg.path))
        for template in templates:
            row = template.snapshot or {}
            if "owner" not in row:
                continue
            try:
                validate_level_params(row, row["owner"] + ":template")
            except SnapshotError as error:
                fail(error.code, error.detail, str(template.path))
                continue
            declared_levels = row.get("level_params", []) + row.get("extra_level_params", []) if isinstance(row.get("level_params", []), list) and isinstance(row.get("extra_level_params", []), list) else []
            template.name = row.get("name", "")
            template.version = row.get("version", 1)
            template.constructors = row.get("constructors", [])
            universes = row.get("enrollment_universes")
            if not isinstance(universes, list) or len(universes) != 2:
                fail("missing_material", "template enrollment universe arguments", str(template.path))
            else:
                for index, universe in enumerate(universes):
                    try:
                        validate_universe_text(universe, f"enrollment_universes[{index}]")
                    except SnapshotError as error:
                        fail(error.code, f"{row['owner']}:{error.detail}", str(template.path))
            if target_uses_controlled_printing(row, "name") and row.get("template_term") is not None:
                try:
                    closed_printed_term(row["template_term"], "template_term")
                    validate_expression_levels(row["template_term"], declared_levels, "template_term")
                    row["printed_template_term"] = True
                except SnapshotError as error:
                    fail(error.code, "template_term", str(template.path))
            constructor_types = row.get("constructor_types", {})
            if isinstance(constructor_types, list):
                row["constructor_name_components"] = {item["name"]: item["name_components"] for item in constructor_types if "name_components" in item}
                constructor_types = {item["name"]: item["type"] for item in constructor_types}
            row["constructor_types"] = constructor_types
            slots = row.get("parser_slots", {})
            printed_constructors = []
            for index, name in enumerate(template.constructors):
                source_type = slots.get(f"constructor_{index}")
                if source_type is not None:
                    constructor_types[name] = source_type
                elif name not in constructor_types or constructor_types[name] is None:
                    fail("missing_material", "constructor type:" + name, str(template.path))
                else:
                    try:
                        closed_printed_term(constructor_types[name], "constructor_types:" + name)
                        validate_expression_levels(constructor_types[name], declared_levels, "constructor_types:" + name)
                        printed_constructors.append(name)
                    except SnapshotError as error:
                        fail(error.code, "constructor_types:" + name, str(template.path))
            row["printed_constructors"] = printed_constructors
            if not template.name or type(template.version) is not int or template.version < 0 or not isinstance(template.constructors, list):
                fail("missing_material", "template name/version/constructors", str(template.path))
        mapping: dict[str, Any] = {}
        if self.mapping_path is None:
            fail("mapping_required", "root-kind-mapping.json is required")
        else:
            mapping = json.loads(self.mapping_path.read_bytes())
        modules = mapping.get("modules", [])
        if not isinstance(modules, list):
            fail("invalid_root_mapping", "modules must be an array")
            modules = []
        by_path: dict[str, dict[str, Any]] = {}
        destinations: set[str] = set()
        for entry in modules:
            relative = relative_reg_path(entry.get("current_path"))
            if relative in by_path:
                fail("duplicate_root_mapping", relative)
            by_path[relative] = entry
            destination = relative_reg_path(entry.get("destination_path"))
            if destination in destinations:
                fail("mapping_collision", destination)
            destinations.add(destination)
            kind = entry.get("kind")
            leaf = "SealedCatalog.lean" if kind == "sealed_catalog" else "RootCatalog.lean"
            if kind not in {"catalog", "sealed_catalog"} or not destination.startswith("Reg/Catalogs/") or Path(destination).name != leaf:
                fail("mapping_outside_catalogs", destination)
            if entry.get("destination_module") != source_module(destination):
                fail("wrong_catalog_owner", destination)
            if entry.get("root_id_after", source_module(destination)) != source_module(destination):
                fail("wrong_root_owner", destination)
            if entry.get("current_module", source_module(relative)) != source_module(relative):
                fail("wrong_source_owner", relative)
            if relative.startswith("Reg/D5/"):
                if entry.get("retained_leaf_path", relative) != relative or entry.get("operation", "split_catalog_from_d5_mirror") != "split_catalog_from_d5_mirror":
                    fail("wrong_mirror_owner", relative)
            elif relative.startswith("Reg/Catalogs/"):
                if entry.get("retained_leaf_path") is not None or entry.get("operation", "relocate_catalog") != "relocate_catalog":
                    fail("wrong_relocation_owner", relative)
        root_paths = {root.path.relative_to(self.repo).as_posix() for root in roots}
        for relative in sorted(set(by_path) - root_paths):
            fail("extra_root_mapping", relative)
        for root in roots:
            relative = root.path.relative_to(self.repo).as_posix()
            entry = by_path.get(relative)
            row = root.snapshot or {}
            if entry is None:
                fail("missing_root_mapping", relative)
                continue
            root.root_id = row.get("root_id", "")
            if root.root_id != source_module(relative) or entry.get("root_id_before", root.root_id) != root.root_id:
                fail("wrong_root_owner", relative)
            root.kind = entry["kind"]
            root.destination_path = entry["destination_path"]
            root.destination_module = entry["destination_module"]
            root.imports = list(entry.get("imports", []))
            if relative.startswith("Reg/D5/") and source_module(relative) not in root.imports:
                root.imports.append(source_module(relative))
            root.companion_prefix = row.get("companion_prefix") or None
            for role in ("expected", "source", "baseline"):
                array = row.get(role)
                if not isinstance(array, list) or any(not isinstance(item, dict) for item in array):
                    fail("missing_material", f"{root.root_id}:{role}")
                    continue
                setattr(root, role, [dict(item) for item in array])
                owners = (entry.get("registration_module_name_after") or {}).get(role)
                occurrence_mapping = (entry.get("occurrence_mapping") or {}).get(role)
                if owners is not None and (not isinstance(owners, list) or len(owners) != len(array)):
                    fail("mapping_occurrence_count_mismatch", f"{root.root_id}:{role}")
                    continue
                if occurrence_mapping is not None and (not isinstance(occurrence_mapping, list) or len(occurrence_mapping) != len(array)):
                    fail("mapping_occurrence_count_mismatch", f"{root.root_id}:{role}")
                    continue
                for index, occurrence in enumerate(array):
                    try:
                        validate_level_params(occurrence, f"{root.root_id}:{role}:{index}")
                    except SnapshotError as error:
                        fail(error.code, error.detail)
                    consumed_fields = ["captured_statement"]
                    if not occurrence.get("proof") and target_uses_controlled_printing(occurrence):
                        consumed_fields.append("target_term")
                    for field in consumed_fields:
                        if occurrence.get(field) is not None:
                            try:
                                closed_printed_term(occurrence[field], field)
                                validate_expression_levels(occurrence[field], occurrence.get("level_params", []), field)
                            except SnapshotError as error:
                                fail(error.code, f"{root.root_id}:{role}:{index}:{field}")
                    owner = occurrence.get("registration_module")
                    after = owners[index] if owners is not None else owner
                    if not isinstance(owner, str) or not owner or not isinstance(after, str) or not after or after == root.destination_module:
                        fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}")
                    if occurrence_mapping is not None:
                        mapped = occurrence_mapping[index]
                        for field in ("theorem", "object_arena", "statement_identity"):
                            if mapped.get(field) != occurrence.get(field):
                                fail("mapping_occurrence_mismatch", f"{root.root_id}:{role}:{index}:{field}")
                        if mapped.get("registration_module_name") != owner or mapped.get("registration_module_name_after") != after:
                            fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}")
                    elif after != owner:
                        fail("unauthorized_owner_correction", f"{root.root_id}:{role}:{index}")
                    if after != owner:
                        matches = [registration for registration in snapshot["registrations"]
                                   if registration.get("owner") == after
                                   and registration.get("registration_module", after) == after
                                   and registration.get("theorem") == occurrence.get("theorem")
                                   and (registration.get("object_arena") or registration.get("resolved_arena") or registration.get("arena")) == occurrence.get("object_arena")]
                        if not matches:
                            fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}:corrected owner has no matching registration")
                    copied = getattr(root, role)[index]
                    copied["registration_module"] = after
                    if after != owner:
                        owning_names = matches[0].get("name_components", {}) if matches else {}
                        original_names = copied.get("name_components", {})
                        if isinstance(original_names, dict):
                            copied["name_components"] = {**original_names}
                            if isinstance(owning_names, dict) and "owner" in owning_names:
                                copied["name_components"]["registration_module"] = owning_names["owner"]
                            else:
                                copied["name_components"].pop("registration_module", None)
                root.registration_module_names[role] = list(owners or [item.get("registration_module", "") for item in array])
        for root in roots:
            owned_seals = [seal for seal in seals if seal.path == root.path]
            if root.kind == "sealed_catalog" and len(owned_seals) != 1:
                fail("missing_seal" if not owned_seals else "duplicate_seal", root.root_id)
            if root.kind == "catalog" and owned_seals:
                fail("unexpected_seal", root.root_id)
            if owned_seals:
                root.seal_options = owned_seals[0].options
        for seal in seals:
            if not any(root.path == seal.path for root in roots):
                fail("missing_root_for_seal", seal.root_id)
            if seal.snapshot and seal.snapshot.get("root_id") != seal.root_id:
                fail("wrong_seal_owner", seal.root_id)

        # Only parser-observed users of recorder companions require an ordinary
        # definition. Compiled bindings resolve the identifiers, so Python never
        # guesses a namespace or strips field projections from source text.
        parser_consumers: set[tuple[str, int, int]] = set()
        existing_names: dict[str, set[str]] = defaultdict(set)
        for source_file in syntax["files"]:
            relative = source_file["path"]
            for command in source_file["commands"]:
                existing_names[relative].update(command.get("declared_names", []))
                name_slot = (command.get("slots") or {}).get("name")
                if command["kind"] == "context" and name_slot:
                    existing_names[relative].add(name_slot.get("text", ""))
                for identifier in command.get("companion_identifiers", command.get("identifiers", [])):
                    start, end = identifier.get("start"), identifier.get("end")
                    byte_slice(originals[relative], start, end, "companion identifier")
                    parser_consumers.add((relative, start, end))
        companions = snapshot.get("companions", [])
        bindings = snapshot.get("companion_bindings", [])
        if not isinstance(companions, list) or not isinstance(bindings, list):
            fail("invalid_companion_snapshot", "companions and companion_bindings must be arrays")
            companions, bindings = [], []
        binding_locations: set[tuple[str, int, int]] = set()
        required_names: set[str] = set()
        for binding in bindings:
            relative = relative_reg_path(binding.get("path"))
            key = (relative, binding.get("start"), binding.get("end"))
            if key in binding_locations:
                fail("duplicate_companion_binding", str(key))
            binding_locations.add(key)
            if key not in parser_consumers:
                fail("extra_companion_binding", str(key))
            name = binding.get("name")
            if not isinstance(name, str) or not name:
                fail("missing_companion_name", str(key))
            else:
                required_names.add(name.removeprefix("_root_."))
        for key in sorted(parser_consumers - binding_locations):
            fail("missing_compiled_companion", str(key))
        companion_index: dict[str, dict[str, Any]] = {}
        dependencies: dict[str, list[str]] = {}
        for companion in companions:
            name, owner = companion.get("name"), companion.get("owner")
            if not isinstance(name, str) or not name or not isinstance(owner, str) or not owner:
                fail("missing_companion_name", repr(companion))
                continue
            canonical_name = name.removeprefix("_root_.")
            if canonical_name in companion_index:
                fail("duplicate_companion", canonical_name)
                continue
            companion_index[canonical_name] = companion
            values = companion.get("companion_dependencies", companion.get("dependencies", []))
            if not isinstance(values, list) or any(not isinstance(value, str) or not value for value in values):
                fail("invalid_companion_dependencies", canonical_name)
                values = []
            canonical_dependencies = [value.removeprefix("_root_.") for value in values]
            if len(canonical_dependencies) != len(set(canonical_dependencies)):
                fail("duplicate_companion_dependency", canonical_name)
            dependencies[canonical_name] = sorted(set(canonical_dependencies))
        visit_state: dict[str, int] = {}
        ordered_names: list[str] = []

        def visit(name: str, parent: str | None = None) -> None:
            if name not in companion_index:
                fail("missing_companion_dependency" if parent else "missing_compiled_companion", name)
                return
            if visit_state.get(name) == 1:
                fail("companion_cycle", name)
                return
            if visit_state.get(name) == 2:
                return
            visit_state[name] = 1
            for dependency in dependencies[name]:
                visit(dependency, name)
            visit_state[name] = 2
            ordered_names.append(name)

        for name in sorted(required_names):
            visit(name)
        for name in sorted(set(companion_index) - set(visit_state)):
            fail("unreferenced_companion", name)
        inline_names = {(item.snapshot or {}).get("realization"): item for item in registrations if item.inline_bridge}
        helper_registrations: dict[str, Registration] = {}
        for canonical_name in ordered_names:
            companion = companion_index[canonical_name]
            name, owner = companion["name"], companion["owner"]
            anchor = companion.get("anchor_unit", canonical_name)
            if not isinstance(anchor, str) or not anchor:
                fail("missing_companion_anchor", canonical_name)
                continue
            anchor = anchor.removeprefix("_root_.")
            matches = [item for item in registrations if (item.snapshot or {}).get("owner") == owner
                       and (item.snapshot or {}).get("unit") == anchor]
            if not matches:
                fail("missing_companion_registration", canonical_name)
                continue
            registration = min(matches, key=lambda item: item.span.start)
            helper_registrations[canonical_name] = registration
            relative = registration.path.relative_to(self.repo).as_posix()
            if canonical_name in existing_names[relative] or name in existing_names[relative]:
                fail("name_collision", canonical_name, relative)
            try:
                validate_level_params(companion, canonical_name)
            except SnapshotError as error:
                fail("invalid_companion_levels", canonical_name)
                continue
            body = companion.get("body", companion.get("value"))
            for field, value in (("type", companion.get("type")), ("body", body)):
                try:
                    if closed_printed_term(value, canonical_name + ":" + field) is None:
                        fail("missing_companion_term", canonical_name + ":" + field)
                    validate_expression_levels(value, companion.get("level_params", []), canonical_name + ":" + field)
                except SnapshotError as error:
                    fail(error.code, canonical_name + ":" + field)
            # The inline source proof already recreates its original declaration.
            # Its dependent units require that name, but need no second definition.
            if canonical_name in inline_names:
                if inline_names[canonical_name] is not registration:
                    fail("wrong_companion_anchor", canonical_name)
                continue
            helper = {**companion, "name": "_root_." + canonical_name, "body": body}
            registration.snapshot.setdefault("companion_helpers", []).append(helper)
            registration.controlled_printing.extend(["companion:" + canonical_name + ":type", "companion:" + canonical_name + ":body"])
        for name, registration in helper_registrations.items():
            for dependency in dependencies[name]:
                predecessor = helper_registrations.get(dependency)
                if predecessor and predecessor.path == registration.path and predecessor.span.start > registration.span.start:
                    fail("companion_order_conflict", name + ":" + dependency)
        for registration in registrations:
            if registration.inline_bridge:
                inline_name = (registration.snapshot or {}).get("realization")
                relative = registration.path.relative_to(self.repo).as_posix()
                if inline_name in existing_names[relative] or "_root_." + str(inline_name) in existing_names[relative]:
                    fail("name_collision", str(inline_name), relative)

        if failures:
            audit = {"snapshot_sha256": input_sha, "source_registrations": len(registrations),
                     "compiled_registrations": len(snapshot["registrations"]), "templates": len(templates),
                     "roots": len(roots), "seals": len(seals), "d5_writes": 0,
                     "compile_blockers": compile_blockers, "reconciliation": [], "source_specializations": [],
                     "missing": sum(item.code == "missing_compiled_input" for item in failures),
                     "extra": sum(item.code == "extra_compiled_input" for item in failures),
                     "duplicate": sum(item.code == "duplicate" for item in failures),
                     "ambiguous": sum(item.code == "ambiguous_compiled_input" for item in failures)}
            return PlanResult(input_sha, registrations, templates, roots, seals, [], failures, audit)

        replacements: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
        reconciliation: list[dict[str, Any]] = []

        def reconcile(category: str, item: Any, output_path: str, output_owner: str,
                      output_decl: str, identity: dict[str, Any]) -> None:
            row = item.snapshot or {}
            reconciliation.append({"category": category, "owner": row["owner"],
                                   "source_index": row["source_index"],
                                   "source_path": item.path.relative_to(self.repo).as_posix(),
                                   "source_span": {"start": item.span.start, "end": item.span.end},
                                   "output_path": output_path, "output_owner": output_owner,
                                   "output_decl": output_decl, "identity": identity})

        declared_names: dict[str, set[str]] = defaultdict(set)
        for file in syntax["files"]:
            for command in file["commands"]:
                declared_names[file["path"]].update(command.get("declared_names", []))
                if command["kind"] == "context":
                    name_slot = (command.get("slots") or {}).get("name")
                    if name_slot:
                        declared_names[file["path"]].add(name_slot.get("text", ""))
        by_path: dict[str, list[Registration]] = defaultdict(list)
        for item in registrations:
            by_path[item.path.relative_to(self.repo).as_posix()].append(item)
        for relative in sorted(by_path):
            for index, item in enumerate(sorted(by_path[relative], key=lambda item: item.span.start)):
                name = f"registration_{index + 1}"
                _, full_name = generated_declaration_name(item.snapshot or {}, name)
                if name in declared_names[relative] or full_name in declared_names[relative]:
                    fail("name_collision", full_name, relative)
                replacements[relative].append((item.span.start, item.span.end, render_registration(item, index)))
                row = item.snapshot or {}
                reconcile("registrations", item, relative, row["owner"], full_name,
                          {"theorem": item.theorem, "unit": row.get("unit"),
                           "object_arena": row.get("object_arena"), "catalog": row.get("catalog"),
                           "statement_identity": row.get("statement_identity")})
        by_templates: dict[str, list[Template]] = defaultdict(list)
        for item in templates:
            by_templates[item.path.relative_to(self.repo).as_posix()].append(item)
        for relative in sorted(by_templates):
            for index, item in enumerate(sorted(by_templates[relative], key=lambda item: item.span.start)):
                name = f"enrollment_{index + 1}"
                _, full_name = generated_declaration_name(item.snapshot or {}, name)
                if name in declared_names[relative] or full_name in declared_names[relative]:
                    fail("name_collision", full_name, relative)
                replacements[relative].append((item.span.start, item.span.end, render_template(item, index)))
                reconcile("templates", item, relative, (item.snapshot or {})["owner"], full_name,
                          {"template": item.name, "version": item.version, "constructors": list(item.constructors)})
        for item in [*roots, *seals]:
            relative = item.path.relative_to(self.repo).as_posix()
            wrappers = (item.snapshot or {}).get("scope_wrappers", [])
            start = min([item.span.start] + [wrapper["start"] for wrapper in wrappers])
            replacements[relative].append((start, item.span.end, ""))
        parsed_imports = {file["path"]: set(file.get("imports", [])) for file in syntax["files"]}
        files: list[GeneratedFile] = []
        for relative in sorted(replacements):
            rendered = replace_spans(originals[relative], replacements[relative])
            required_imports: set[str] = set()
            if relative in by_path:
                required_imports.add("LeanInformationAuditInterface.Contract.Registration")
            if relative in by_templates:
                required_imports.add("LeanInformationAuditInterface.Contract.Catalog")
            missing_imports = sorted(required_imports - parsed_imports[relative])
            if missing_imports:
                rendered = "".join(f"import {module}\n" for module in missing_imports) + rendered
            files.append(GeneratedFile(relative, rendered, "leaf"))
        for root in sorted(roots, key=lambda item: item.destination_path or ""):
            if root.destination_path and root.destination_module:
                files.append(GeneratedFile(root.destination_path, render_root(root, root.kind, root.destination_module), "root"))
                identity = {"root_id_before": root.root_id, "root_id_after": root.destination_module,
                            "occurrences": {}}
                for role in ("expected", "source", "baseline"):
                    original_rows = (root.snapshot or {})[role]
                    identity["occurrences"][role] = [
                        {"index": index, "theorem": row["theorem"], "object_arena": row["object_arena"],
                         "statement_identity": row.get("statement_identity"),
                         "registration_module_before": original_rows[index]["registration_module"],
                         "registration_module_after": row["registration_module"]}
                        for index, row in enumerate(getattr(root, role))]
                reconcile("roots", root, root.destination_path, root.destination_module,
                          root.destination_module + ".rootCatalog", identity)
                for seal in sorted((item for item in seals if item.path == root.path), key=lambda item: item.span.start):
                    reconcile("seals", seal, root.destination_path, root.destination_module,
                              root.destination_module + ".seal",
                              {"root_id_before": seal.root_id, "root_id_after": root.destination_module})
        paths: set[str] = set()
        for file in files:
            relative_reg_path(file.path)
            if file.path in paths:
                fail("output_collision", file.path)
            paths.add(file.path)
            current = self.repo / file.path
            if file.path not in originals and current.exists() and current.read_text(encoding="utf-8") != file.text:
                fail("destination_exists", file.path)
        generated = {file.path: file.text for file in files}
        for relative, original in sorted(originals.items()):
            current = self.repo / relative
            if not current.is_file():
                fail("missing_source_file", relative)
                continue
            content = current.read_bytes()
            if content != original.encode("utf-8") and content != generated.get(relative, original).encode("utf-8"):
                fail("source_snapshot_mismatch", relative)
        actual_paths = {path.relative_to(self.repo).as_posix() for path in (self.repo / "Reg").rglob("*.lean")}
        for relative in sorted(actual_paths - set(originals) - paths):
            fail("extra_source_file", relative)
        print_rows = [{"owner": item.module_name, "source_index": (item.snapshot or {}).get("source_index"),
                       "theorem": item.theorem, "fields": sorted(item.controlled_printing)}
                      for item in registrations if item.controlled_printing]
        for template in templates:
            printed_constructors = (template.snapshot or {}).get("printed_constructors", [])
            fields = ["constructor_types:" + name for name in printed_constructors]
            if (template.snapshot or {}).get("printed_template_term"):
                fields.append("template_term")
            if fields:
                print_rows.append({"owner": (template.snapshot or {}).get("owner"),
                                   "source_index": (template.snapshot or {}).get("source_index"),
                                   "template": template.name, "fields": fields})
        for root in roots:
            fields = [f"{role}[{index}].captured_statement" for role in ("expected", "source", "baseline")
                      for index, row in enumerate(getattr(root, role)) if row.get("captured_statement") is not None]
            fields += [f"{role}[{index}].target_term" for role in ("expected", "source", "baseline")
                       for index, row in enumerate(getattr(root, role))
                       if not row.get("proof") and target_uses_controlled_printing(row) and row.get("target_term") is not None]
            if fields:
                print_rows.append({"owner": root.root_id, "source_index": (root.snapshot or {}).get("source_index"),
                                   "root": root.root_id, "fields": fields})
        changed_files = [file for file in files if not (self.repo / file.path).is_file()
                         or (self.repo / file.path).read_bytes() != file.text.encode("utf-8")]
        audit = {"snapshot_sha256": input_sha, "changed_files": len(changed_files),
                 "companion_inputs": len(companions), "companion_helpers": sum(len((item.snapshot or {}).get("companion_helpers", [])) for item in registrations), "companion_consumers": len(parser_consumers),
                 "source_registrations": len(registrations), "compiled_registrations": len(snapshot["registrations"]),
                 "templates": len(templates), "compiled_templates": len(snapshot["templates"]),
                 "roots": len(roots), "compiled_roots": len(snapshot["roots"]),
                 "seals": len(seals), "compiled_seals": len(snapshot["seals"]), "notations": len(notations),
                 "missing": sum(failure.code == "missing_compiled_input" for failure in failures),
                 "extra": sum(failure.code == "extra_compiled_input" for failure in failures),
                 "duplicate": sum(failure.code == "duplicate" for failure in failures),
                 "ambiguous": sum(failure.code == "ambiguous_compiled_input" for failure in failures),
                 "d5_writes": 0, "controlled_printing": print_rows, "compile_blockers": compile_blockers,
                 "source_specializations": [] if failures else sorted(specialization_audit, key=lambda row:
                     (row["category"], row["owner"], row["source_index"], row["slot"])),
                 "reconciliation": [] if failures else sorted(reconciliation, key=lambda row:
                     (("registrations", "templates", "roots", "seals").index(row["category"]), row["owner"], row["source_index"])),
                 "source_sha256": {path: _sha256_text(text) for path, text in sorted(originals.items())},
                 "mapping_sha256": sha256_file(self.mapping_path) if self.mapping_path else None}
        # A failed plan exposes diagnostics but no writeable file set.
        return PlanResult(input_sha, registrations, templates, roots, seals,
                          [] if failures else sorted(changed_files, key=lambda file: file.path), failures, audit)

    def write(self, result: PlanResult, output: Path, apply_root: Path | None = None) -> None:
        if result.failures:
            raise GeneratorFailure("refusing to write with failures")
        if not result.files:
            return
        target = apply_root.resolve() if apply_root else output.resolve()
        # Preflight the entire output set before the first directory or file write.
        planned: list[tuple[Path, bytes]] = []
        for generated in result.files:
            relative_reg_path(generated.path)
            path = target / generated.path
            if path.is_symlink() or any(parent.is_symlink() for parent in path.parents if parent != target.parent):
                raise GeneratorFailure(f"unsafe_output_path: {generated.path}")
            if path.exists() and not path.is_file():
                raise GeneratorFailure(f"output_not_file: {generated.path}")
            if apply_root and path.exists() and generated.path not in result.audit.get("source_sha256", {}) and path.read_bytes() != generated.text.encode("utf-8"):
                raise GeneratorFailure(f"destination_exists: {generated.path}")
            if apply_root and path.exists() and generated.path in result.audit.get("source_sha256", {}):
                current_sha = hashlib.sha256(path.read_bytes()).hexdigest()
                if current_sha not in {result.audit["source_sha256"][generated.path], _sha256_text(generated.text)}:
                    raise GeneratorFailure(f"source_snapshot_mismatch: {generated.path}")
            planned.append((path, generated.text.encode("utf-8")))
        report = {"input_sha256": result.input_sha256, "audit": result.audit, "failures": [],
                  "files": [{"path": file.path, "kind": file.kind, "sha256": _sha256_text(file.text)} for file in result.files]}
        planned.append((target / "p2b-audit.json", (json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")))
        for path, _ in planned:
            if path.exists() and not path.is_file():
                raise GeneratorFailure(f"output_not_file: {path.name}")
        for path, data in planned:
            if path.exists() and path.read_bytes() == data:
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            temporary = path.with_name(path.name + ".tmp")
            temporary.write_bytes(data)
            temporary.replace(path)
