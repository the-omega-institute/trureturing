from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .lean_syntax import (load_syntax_snapshot, parse_repository, relative_reg_path,
                          source_module, syntax_sources)
from .model import Failure, GeneratedFile, PlanResult, Registration, Root, Seal, Template
from .render import render_registration, render_root, render_template, replace_spans
from .snapshot import SnapshotError, closed_printed_term, load_input_snapshot, sha256_file, typed_options


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
            return PlanResult("", [], [], [], [], [], [Failure(error.code, error.path, error.detail)], {})
        except (OSError, ValueError, KeyError, TypeError) as error:
            return PlanResult("", [], [], [], [], [], [Failure("invalid_snapshot", str(self.inputs_path), str(error))], {})

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
                    elif isinstance(captured, str) and captured != original:
                        candidates = [position for position, item in enumerate(source_items)
                                      if getattr(item, "source_text", None) == captured]
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
                    if source_required and captured not in {original, getattr(item, "source_text", None)}:
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
                    item.snapshot = {**row, **parser_metadata}
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
        for reg in registrations:
            row = reg.snapshot or {}
            if "owner" not in row:
                continue
            if row.get("registration_module", row["owner"]) != row["owner"]:
                fail("wrong_registration_owner", str(row.get("registration_module")), str(reg.path))
            theorem = row.get("theorem")
            if not isinstance(theorem, str) or not theorem:
                fail("missing_material", "compiled theorem name", str(reg.path))
            else:
                reg.theorem = theorem
            universes, arguments = row.get("registration_universes"), row.get("type_args")
            if not isinstance(universes, list) or len(universes) != 17 or not isinstance(arguments, list) or len(arguments) != 8:
                fail("missing_material", "registration universe/type arguments", str(reg.path))
            else:
                for index, value in enumerate(arguments):
                    try:
                        closed_printed_term(value, f"type_args[{index}]")
                        reg.controlled_printing.append(f"type_args[{index}]")
                    except SnapshotError as error:
                        fail(error.code, f"{reg.module_name}:type_args[{index}]", str(reg.path))
            reg.catalog = row.get("catalog", reg.catalog)
            reg.native = reg.variant == "native"
            slots = row.get("parser_slots", {})
            if row.get("open_continuation") and not reg.continuation:
                reg.continuation = "open"
            for field in ("bridge_arena", "inline_bridge_type"):
                if field == "bridge_arena" and row.get("bridge_arena_from_source"):
                    continue
                if row.get(field) is not None:
                    try:
                        closed_printed_term(row[field], field)
                        reg.controlled_printing.append(field)
                    except SnapshotError as error:
                        fail(error.code, f"{reg.module_name}:{field}", str(reg.path))
            if reg.inline_bridge:
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
            template.name = row.get("name", "")
            template.version = row.get("version", 1)
            template.constructors = row.get("constructors", [])
            constructor_types = row.get("constructor_types", {})
            if isinstance(constructor_types, list):
                constructor_types = {item["name"]: item["type"] for item in constructor_types}
            row["constructor_types"] = constructor_types
            for name in template.constructors:
                if name not in constructor_types:
                    fail("missing_material", "constructor type:" + name, str(template.path))
                else:
                    try:
                        closed_printed_term(constructor_types[name], "constructor_types:" + name)
                    except SnapshotError as error:
                        fail(error.code, "constructor_types:" + name, str(template.path))
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
                    if occurrence.get("captured_statement") is not None:
                        try:
                            closed_printed_term(occurrence["captured_statement"], "captured_statement")
                        except SnapshotError as error:
                            fail(error.code, f"{root.root_id}:{role}:{index}:captured_statement")
                    owner = occurrence.get("registration_module")
                    if not isinstance(owner, str) or not owner or owner == root.destination_module:
                        fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}")
                    if owners is not None and owners[index] != owner:
                        fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}")
                    if occurrence_mapping is not None:
                        mapped = occurrence_mapping[index]
                        for field in ("theorem", "object_arena", "statement_identity"):
                            if mapped.get(field) != occurrence.get(field):
                                fail("mapping_occurrence_mismatch", f"{root.root_id}:{role}:{index}:{field}")
                        if mapped.get("registration_module_name_after") != owner:
                            fail("wrong_occurrence_owner", f"{root.root_id}:{role}:{index}")
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

        if failures:
            audit = {"snapshot_sha256": input_sha, "source_registrations": len(registrations),
                     "compiled_registrations": len(snapshot["registrations"]), "templates": len(templates),
                     "roots": len(roots), "seals": len(seals), "d5_writes": 0,
                     "missing": sum(item.code == "missing_compiled_input" for item in failures),
                     "extra": sum(item.code == "extra_compiled_input" for item in failures),
                     "duplicate": sum(item.code == "duplicate" for item in failures),
                     "ambiguous": sum(item.code == "ambiguous_compiled_input" for item in failures)}
            return PlanResult(input_sha, registrations, templates, roots, seals, [], failures, audit)

        replacements: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
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
                namespace = (item.snapshot or {}).get("namespace", "")
                full_name = f"{namespace}.{name}" if namespace else name
                if name in declared_names[relative] or full_name in declared_names[relative]:
                    fail("name_collision", full_name, relative)
                replacements[relative].append((item.span.start, item.span.end, render_registration(item, index)))
        by_templates: dict[str, list[Template]] = defaultdict(list)
        for item in templates:
            by_templates[item.path.relative_to(self.repo).as_posix()].append(item)
        for relative in sorted(by_templates):
            for index, item in enumerate(sorted(by_templates[relative], key=lambda item: item.span.start)):
                name = f"enrollment_{index + 1}"
                if name in declared_names[relative]:
                    fail("name_collision", name, relative)
                replacements[relative].append((item.span.start, item.span.end, render_template(item, index)))
        for item in [*roots, *seals]:
            relative = item.path.relative_to(self.repo).as_posix()
            replacements[relative].append((item.span.start, item.span.end, ""))
        files: list[GeneratedFile] = []
        for relative in sorted(replacements):
            rendered = replace_spans(originals[relative], replacements[relative])
            files.append(GeneratedFile(relative, rendered, "leaf"))
        for root in sorted(roots, key=lambda item: item.destination_path or ""):
            if root.destination_path and root.destination_module:
                files.append(GeneratedFile(root.destination_path, render_root(root, root.kind, root.destination_module), "root"))
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
            if template.constructors:
                print_rows.append({"owner": (template.snapshot or {}).get("owner"),
                                   "source_index": (template.snapshot or {}).get("source_index"),
                                   "template": template.name, "fields": ["constructor_types:" + name for name in template.constructors]})
        for root in roots:
            fields = [f"{role}[{index}].captured_statement" for role in ("expected", "source", "baseline")
                      for index, row in enumerate(getattr(root, role)) if row.get("captured_statement") is not None]
            if fields:
                print_rows.append({"owner": root.root_id, "source_index": (root.snapshot or {}).get("source_index"),
                                   "root": root.root_id, "fields": fields})
        changed_files = [file for file in files if not (self.repo / file.path).is_file()
                         or (self.repo / file.path).read_bytes() != file.text.encode("utf-8")]
        audit = {"snapshot_sha256": input_sha, "changed_files": len(changed_files),
                 "source_registrations": len(registrations), "compiled_registrations": len(snapshot["registrations"]),
                 "templates": len(templates), "compiled_templates": len(snapshot["templates"]),
                 "roots": len(roots), "compiled_roots": len(snapshot["roots"]),
                 "seals": len(seals), "compiled_seals": len(snapshot["seals"]), "notations": len(notations),
                 "missing": sum(failure.code == "missing_compiled_input" for failure in failures),
                 "extra": sum(failure.code == "extra_compiled_input" for failure in failures),
                 "duplicate": sum(failure.code == "duplicate" for failure in failures),
                 "ambiguous": sum(failure.code == "ambiguous_compiled_input" for failure in failures),
                 "d5_writes": 0, "controlled_printing": print_rows,
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
