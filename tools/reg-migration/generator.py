from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .lean_syntax import parse_repository
from .model import Failure, GeneratedFile, PlanResult, Registration, Root, Seal, Template
from .render import render_registration, render_root, render_seal, render_template, replace_spans
from .snapshot import index_rows, load_input_snapshot, load_report, registration_rows, sha256_file


class GeneratorFailure(RuntimeError):
    pass


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Generator:
    def __init__(self, repo: Path, report: Path, mapping: Path | None = None, inputs: Path | None = None, root_inventory: Path | None = None):
        self.repo = repo.resolve()
        self.report_path = report.resolve()
        self.mapping_path = mapping.resolve() if mapping else None
        self.inputs_path = inputs.resolve() if inputs else None
        self.root_inventory_path = root_inventory.resolve() if root_inventory else None

    def plan(self, expected_sha256: str | None = None) -> PlanResult:
        registrations, templates, roots, seals, notations = parse_repository(self.repo)
        for registration in registrations:
            if not registration.theorem:
                failures = [Failure("unknown_registration_shape", str(registration.path), "theorem identifier is missing")]
                return PlanResult("", registrations, templates, roots, seals, [], failures, {})
            if not registration.arena:
                failures = [Failure("unknown_registration_shape", str(registration.path), f"{registration.theorem}: arena is missing")]
                return PlanResult("", registrations, templates, roots, seals, [], failures, {})
        report, report_sha = load_report(self.report_path)
        if expected_sha256 and expected_sha256 != report_sha:
            failure = Failure("snapshot_sha_mismatch", str(self.report_path), f"expected {expected_sha256}, got {report_sha}")
            return PlanResult(report_sha, registrations, templates, roots, seals, [], [failure], {"sha256": report_sha})
        rows = registration_rows(report)
        index, duplicates = index_rows(rows)
        failures: list[Failure] = [Failure("duplicate", str(self.report_path), json.dumps(row, sort_keys=True)) for _, row in duplicates]
        seen: Counter[tuple[str, str, str, str, str]] = Counter()
        for registration in registrations:
            key_candidates = [
                key for key in index
                if key[1] == registration.module_name and (
                    key[2] == registration.theorem
                    or key[2].endswith("." + registration.theorem)
                    or registration.theorem.endswith("." + key[2])
                )
            ]
            if not key_candidates:
                short = registration.theorem.rsplit(".", 1)[-1]
                key_candidates = [key for key in index if key[1] == registration.module_name and key[2].rsplit(".", 1)[-1] == short and key not in seen]
            elif len(key_candidates) > 1:
                unused = [key for key in key_candidates if key not in seen]
                if len(unused) == 1:
                    key_candidates = unused
            if len(key_candidates) == 0:
                failures.append(Failure("missing_compiled_input", str(registration.path), f"{registration.module_name}:{registration.theorem}"))
                continue
            if len(key_candidates) > 1:
                failures.append(Failure("ambiguous_compiled_input", str(registration.path), repr(key_candidates)))
                continue
            key = key_candidates[0]
            registration.snapshot = index[key]
            registration.theorem = key[2]
            seen[key] += 1
        for key in sorted(set(index) - set(seen)):
            failures.append(Failure("extra_compiled_input", str(self.report_path), repr(key)))
        # Roots are keyed by file path and the fix9 mapping is the only source
        # for relocation decisions.  A missing mapping is a hard failure.
        mapping_data: dict[str, Any] = {}
        if self.mapping_path:
            mapping_data = json.loads(self.mapping_path.read_text(encoding="utf-8"))
            modules = mapping_data.get("modules", [])
            by_path = {str(item.get("current_path")): item for item in modules}
            root_paths = {root.path.relative_to(self.repo).as_posix() for root in roots}
            for path in sorted(set(by_path) - root_paths):
                failures.append(Failure("extra_root_mapping", str(self.mapping_path), path))
            for root in roots:
                item = by_path.get(root.path.relative_to(self.repo).as_posix())
                if not item:
                    failures.append(Failure("missing_root_mapping", str(root.path), root.root_id))
                    continue
                root.root_id = str(item.get("root_id_before") or root.root_id)
                root.kind = str(item.get("kind", "ordinary"))
                root.destination_path = item.get("destination_path")
                root.destination_module = item.get("destination_module")
                root.imports = list(item.get("imports", []))
                names = item.get("registration_module_name_after") or {}
                root.registration_module_names = {k: list(v) for k, v in names.items() if isinstance(v, list)}
            if self.root_inventory_path and self.root_inventory_path.exists():
                inventory = json.loads(self.root_inventory_path.read_text(encoding="utf-8"))
                by_owner = {str(item.get("owner")): item for item in inventory if isinstance(item, dict)}
                for root in roots:
                    source = by_owner.get(root.root_id)
                    if source:
                        def literal(rows: list[dict[str, Any]], role: str) -> str:
                            rendered = []
                            owners = root.registration_module_names.get(role, [])
                            for position, row in enumerate(rows):
                                owner = owners[position] if position < len(owners) else row.get("registration_module_name", "")
                                rendered.append("{ objectArenaName := `" + str(row.get("object_arena", "")) +
                                    ", theoremName := `" + str(row.get("theorem", "")) +
                                    ", statementIdentity := \"" + str(row.get("statement_identity", "")) +
                                    "\", registrationModuleName := `" + str(owner) + " }")
                            return "#[" + ", ".join(rendered) + "]"
                        root.expected = literal(source.get("expected", []), "expected")
                        root.source = literal(source.get("source", []), "source")
                        root.baseline = literal(source.get("baseline", []), "baseline")
                    else:
                        failures.append(Failure("missing_root_inventory", str(self.root_inventory_path), root.root_id))
            # mapping itself must be injective and stay inside Reg/Catalogs.
            destinations = [item.get("destination_path") for item in modules if item.get("destination_path")]
            if len(destinations) != len(set(destinations)):
                failures.append(Failure("mapping_collision", str(self.mapping_path), "destination_path is not injective"))
            for item in modules:
                path = str(item.get("destination_path", ""))
                if path and not path.startswith("Reg/Catalogs/"):
                    failures.append(Failure("mapping_outside_catalogs", str(self.mapping_path), path))
        else:
            failures.append(Failure("mapping_required", "", "root-kind-mapping.json is required"))
        snapshot = load_input_snapshot(self.inputs_path)
        if snapshot:
            input_sha = str(snapshot.get("input_sha256", report_sha))
            if input_sha != report_sha:
                failures.append(Failure("input_snapshot_sha_mismatch", str(self.inputs_path), f"{input_sha} != {report_sha}"))
        files: list[GeneratedFile] = []
        by_path: dict[Path, list[Registration]] = defaultdict(list)
        for registration in registrations:
            by_path[registration.path].append(registration)
        for path in sorted(by_path):
            source = path.read_text(encoding="utf-8")
            replacements = [(r.span.start, r.span.end, render_registration(r, i)) for i, r in enumerate(sorted(by_path[path], key=lambda x: x.span.start))]
            files.append(GeneratedFile(path.relative_to(self.repo).as_posix(), replace_spans(source, replacements), "registration"))
        template_by_path: dict[Path, list[Template]] = defaultdict(list)
        for template in templates:
            template_by_path[template.path].append(template)
        template_index = 0
        for path in sorted(template_by_path):
            source = path.read_text(encoding="utf-8")
            replacements = []
            for template in sorted(template_by_path[path], key=lambda x: x.span.start):
                replacements.append((template.span.start, template.span.end, render_template(template, template_index)))
                template_index += 1
            files.append(GeneratedFile(path.relative_to(self.repo).as_posix(), replace_spans(source, replacements), "template"))
        for root in sorted(roots, key=lambda x: x.root_id):
            if root.destination_path and root.destination_module:
                files.append(GeneratedFile(root.destination_path, render_root(root, root.kind, root.destination_module), "root"))
        for seal in sorted(seals, key=lambda x: (str(x.path), x.span.start)):
            # Seal destination follows the mapped root with the same owner.
            destination = seal.root_id
            for root in roots:
                if root.path == seal.path and root.destination_module:
                    destination = root.destination_module
                    break
            if any(root.path == seal.path and root.kind == "sealed_catalog" for root in roots):
                continue
            files.append(GeneratedFile(f"Reg/Catalogs/{destination.removeprefix('Reg.Catalogs.')}/SealedCatalog.lean", render_seal(seal, destination), "seal"))
        # D5 is only a mirror target for existing registrations.  A generator
        # plan must never schedule a direct D5 write.
        for file in files:
            if file.path.startswith("D5/"):
                failures.append(Failure("d5_write", file.path, "generated output must remain under Reg"))
        audit = {
            "snapshot_sha256": report_sha,
            "source_registrations": len(registrations),
            "compiled_registrations": len(rows),
            "templates": len(templates),
            "roots": len(roots),
            "seals": len(seals),
            "notations": len(notations),
            "missing": sum(f.code == "missing_compiled_input" for f in failures),
            "extra": sum(f.code == "extra_compiled_input" for f in failures),
            "duplicate": sum(f.code == "duplicate" for f in failures),
            "ambiguous": sum(f.code == "ambiguous_compiled_input" for f in failures),
            "d5_writes": 0,
            "mapping_sha256": sha256_file(self.mapping_path) if self.mapping_path and self.mapping_path.exists() else None,
        }
        return PlanResult(report_sha, registrations, templates, roots, seals, files, failures, audit)

    def write(self, result: PlanResult, output: Path, apply_root: Path | None = None) -> None:
        if result.failures:
            raise GeneratorFailure("refusing to write with failures")
        target = apply_root.resolve() if apply_root else output.resolve()
        target.mkdir(parents=True, exist_ok=True)
        for generated in result.files:
            path = target / generated.path
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_name(path.name + ".tmp")
            tmp.write_text(generated.text, encoding="utf-8")
            tmp.replace(path)
        report = {
            "input_sha256": result.input_sha256,
            "audit": result.audit,
            "failures": [failure.as_dict() for failure in result.failures],
            "files": [{"path": f.path, "kind": f.kind, "sha256": _sha256_text(f.text)} for f in result.files],
        }
        (target / "p2b-audit.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
