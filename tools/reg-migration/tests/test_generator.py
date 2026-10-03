from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
PACKAGE_DIR = ROOT / "tools" / "reg-migration"
spec = importlib.util.spec_from_file_location("reg_migration", PACKAGE_DIR / "__init__.py", submodule_search_locations=[str(PACKAGE_DIR)])
assert spec and spec.loader
package = importlib.util.module_from_spec(spec)
sys.modules["reg_migration"] = package
spec.loader.exec_module(package)

from reg_migration.generator import Generator, GeneratorFailure
from reg_migration.render import options_literal, replace_spans


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Fixture:
    """Independent compiled-input and Lean-parser snapshot fixtures."""

    def __init__(self, root: Path):
        self.root = root
        self.sources: dict[str, str] = {}
        self.syntax = {"schema": "reg-migration-syntax-v1", "files": []}
        self.raw = {"schema": "reg-migration-inputs-v2", "registrations": [], "templates": [], "roots": [], "seals": [], "expected": []}
        self.mapping = {"modules": []}
        self.inputs_path = root / "compiled inputs.json"
        self.syntax_path = root / "syntax spans.json"
        self.mapping_path = root / "root mapping.json"

    def source(self, path: str, prefix: str = "import LeanInformationAuditInterface.Syntax\n\n") -> dict:
        if path not in self.sources:
            self.sources[path] = prefix
            self.syntax["files"].append({"path": path, "source_text": prefix, "source_sha256": _sha(prefix), "commands": []})
        return next(item for item in self.syntax["files"] if item["path"] == path)

    def command(self, path: str, text: str, kind: str, slots: dict[str, str] | None = None, variant: str = "") -> dict:
        file = self.source(path)
        start = len(self.sources[path].encode("utf-8"))
        self.sources[path] += text + "\n"
        raw = text.encode("utf-8")
        spans = {}
        for key, value in (slots or {}).items():
            relative = raw.index(value.encode("utf-8"))
            spans[key] = {"start": start + relative, "end": start + relative + len(value.encode("utf-8")), "text": value}
        command = {"kind": kind, "variant": variant, "syntax_kind": "synthetic." + kind, "start": start, "end": start + len(raw), "slots": spans}
        file["commands"].append(command)
        return command

    def registration(self, path: str = "Reg/D5/Sample.lean", *, theorem: str = "D5.Sample.claim", variant: str = "legacy", occurrence: int = 0, continuation: str | None = "open", inline: bool = False, readout: str = "Template.realize x", options: list[dict] | None = None) -> dict:
        arena = f"arena{occurrence}" if occurrence else "arena"
        slots = {"theorem": theorem, "arena": arena, "readout": readout}
        text = f"{'information_theorem' if variant == 'native' else 'register_information_theorem'} {theorem} in {arena}"
        if variant == "occurrence":
            slots.update(object_arena=f"objectArena{occurrence}", catalog=f"catalog{occurrence}")
            text += f" object_arena {slots['object_arena']} catalog {slots['catalog']}"
        text += f"\n  readout via ({readout})"
        if variant in {"source", "finite-source"}:
            slots.update(source_record="familyRecord", escape_from_source="selectedSource")
            text += " realizes familyRecord"
            if variant == "finite-source":
                slots.update(finite_bridge="finiteBridge", variation="varying", sensitivity="sensitive")
                text += " finite via finiteBridge variation varying sensitivity sensitive"
            text += "\n  escape from source (selectedSource)"
        else:
            slots.update(primitive="actual" if variant == "native" else "actual.toPrimitiveBundle", variation="varying", sensitivity="sensitive", escape_from="Nat")
            text += "\n  primitives " + slots["primitive"]
            if variant == "native":
                pass
            elif inline:
                slots.update(inline_actual="actual", inline_proof="by exact originalBridge")
                text += " realization inline actual := by exact originalBridge"
            else:
                slots["realization"] = "bridge"
                text += " realization bridge"
            text += " variation varying sensitivity sensitive\n  escape from (Nat)"
        if continuation is not None:
            slots["continuation"] = continuation
            text += f" escape continues ({continuation})"
        if variant == "native":
            slots.update(target_type="∀ (α : Type u) (β : Type v), True", native_proof="by intros; trivial")
            text += " : " + slots["target_type"] + " := " + slots["native_proof"]
        owner = path[:-5].replace("/", ".")
        self.command(path, text, "registration", slots, variant)
        row = {
            "owner": owner, "source_text": text, "theorem": theorem,
            "unit": f"{theorem}.__unit_{occurrence}", "arena": arena,
            "object_arena": slots.get("object_arena", arena), "catalog": slots.get("catalog", arena),
            "resolved_arena": arena, "registration_module": owner,
            "realization": f"{theorem}.__realization_{occurrence}", "realization_source": "finiteBridge" if variant == "finite-source" else "bridge",
            "variation": "varying", "sensitivity": "sensitive", "generated": variant == "native",
            "source_bound": variant in {"source", "finite-source"}, "local_registration_names": variant not in {"source", "occurrence"},
            "statement_identity": "identity-from-compiled-input", "level_params": [],
            "bridge_kind": "legacy" if variant in {"occurrence", "finite-source", "native"} else variant,
            "actual": {"text": "actual", "printed": True, "level_params": []},
            "realization_actual": {"text": "actual", "printed": True, "level_params": []},
            "supplied_primitives": {"text": "actual.toPrimitiveBundle", "printed": True, "level_params": []},
            "registration_universes": ["0"] * 17,
            "type_args": [{"text": "Unit", "printed": True, "level_params": []} for _ in range(8)],
            "options": options or [],
        }
        row["source_index"] = sum(item["owner"] == owner for item in self.raw["registrations"])
        if variant in {"source", "finite-source"}:
            row["source_selection"] = {
                "owner": "D5.Sample", "definition": None, "coordinates": [2, 7],
                "readouts": [{"path": ["body", "arg"], "stateBinder": 1, "functionOperand": False, "stateOperand": None, "booleanPredicate": False}],
            }
        self.raw["registrations"].append(row)
        return row

    def template(self, path: str = "Reg/Support/Template.lean", *, constructors: bool = False) -> dict:
        name = "SyntheticTemplate"
        text = "register_information_template " + name
        slots = {"name": name}
        values = ["SyntheticTemplate.second", "SyntheticTemplate.first"] if constructors else []
        if constructors:
            slots.update(version="7", constructors="[SyntheticTemplate.second, SyntheticTemplate.first]")
            slots.update(constructor_0=values[0], constructor_1=values[1])
            text += " constructors 7 " + slots["constructors"]
        self.command(path, text, "template", slots)
        row = {"owner": path[:-5].replace("/", "."), "name": name, "version": 7 if constructors else 1, "constructors": values,
               "source_index": 0, "options": [], "level_params": [], "source_text": text, "enrollment_universes": ["0", "0"],
               "constructor_types": {name: {"text": "True", "printed": True, "level_params": []} for name in values}}
        self.raw["templates"].append(row)
        return row

    def root_catalog(self, path: str = "Reg/D5/Sample.lean", *, entry: str = "root-literal", sealed: bool = False, rows: list[dict] | None = None) -> dict:
        owner = path[:-5].replace("/", ".")
        literal = "{ rootId := `" + owner + ", expected := #[], source := #[], baseline := #[], companionPrefix := none }"
        if entry == "root-literal":
            text = "run_cmd RootCatalogs.declare " + literal
            slots = {"root_contract": literal}
        elif entry == "root-snapshot":
            text = "run_cmd do\n  let statement ← captureStatement `D5.Sample.claim\n  RootCatalogs.declare " + literal
            slots = {"root_contract": literal}
        else:
            text = "run_cmd RootCatalogs.declare (Support.contract.map fun row => row)"
            slots = {"root_contract": "Support.contract.map fun row => row"}
        self.command(path, text, "root", slots, entry)
        registration = next((row for row in self.raw["registrations"] if row["owner"] == owner), None)
        contributor = owner if path.startswith("Reg/D5/") else "Reg.D5.Sample"
        values = copy.deepcopy(rows or [{"root_id": owner, "object_arena": "arena", "theorem": registration["theorem"] if registration else "D5.Sample.claim",
                                        "statement_identity": "compiled-identity", "registration_module": contributor,
                                        "captured_statement": {"text": "True", "printed": True, "level_params": []}}])
        raw = {"owner": owner, "root_id": owner, "expected": values, "source": copy.deepcopy(values), "baseline": [], "companion_prefix": "", "source_text": text, "source_index": 0}
        self.raw["roots"].append(raw)
        mirrored = path.startswith("Reg/D5/")
        stem = path[:-5]
        catalog_stem = "Reg/Catalogs/D5/" + stem.removeprefix("Reg/D5/") if mirrored else stem
        filename = "SealedCatalog" if sealed else "RootCatalog"
        destination_path = catalog_stem + "/" + filename + ".lean"
        destination = destination_path[:-5].replace("/", ".")
        mapping = {"current_path": path, "current_module": owner, "kind": "sealed_catalog" if sealed else "catalog",
                   "operation": "split_catalog_from_d5_mirror" if mirrored else "relocate_catalog",
                   "root_id_before": owner, "root_id_after": destination, "destination_path": destination_path,
                   "destination_module": destination, "retained_leaf_path": path if mirrored else None, "imports": [owner] if mirrored else [],
                   "registration_module_name_after": {role: [row["registration_module"] for row in raw[role]] for role in ("expected", "source", "baseline")}}
        self.mapping["modules"].append(mapping)
        if sealed:
            self.command(path, "seal_information_catalog", "seal")
            self.raw["seals"].append({"owner": owner, "root_id": owner, "options": [], "source_index": 0})
        return mapping

    def save(self) -> None:
        for path, text in self.sources.items():
            file = self.source(path)
            file.update(source_text=text, source_sha256=_sha(text))
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        for kind in ("registrations", "templates", "roots", "seals"):
            for row in self.raw[kind]:
                path = row["owner"].replace(".", "/") + ".lean"
                if path in self.sources:
                    row["source_text"] = self.sources[path]
        self.inputs_path.write_text(json.dumps(self.raw, ensure_ascii=False), encoding="utf-8")
        self.syntax_path.write_text(json.dumps(self.syntax, ensure_ascii=False), encoding="utf-8")
        self.mapping_path.write_text(json.dumps(self.mapping, ensure_ascii=False), encoding="utf-8")

    def generator(self) -> Generator:
        return Generator(self.root, inputs=self.inputs_path, mapping=self.mapping_path, syntax=self.syntax_path)

    def catalog_owner_correction(self) -> tuple[dict, str, str]:
        leaf = "Reg.D5.Contributor"
        catalog = "Reg.Catalogs.Collected"
        registration = self.registration("Reg/D5/Contributor.lean", theorem="D5.Contributor.claim")
        occurrence = {"root_id": catalog, "object_arena": registration["object_arena"], "theorem": registration["theorem"],
                      "statement_identity": registration["statement_identity"], "registration_module": catalog,
                      "captured_statement": {"text": "True", "printed": True, "level_params": []}}
        mapping = self.root_catalog("Reg/Catalogs/Collected.lean", rows=[occurrence])
        mapping["imports"] = [leaf]
        mapping["occurrence_mapping"] = {}
        for role in ("expected", "source"):
            mapping["registration_module_name_after"][role] = [leaf]
            mapping["occurrence_mapping"][role] = [{"object_arena": occurrence["object_arena"], "theorem": occurrence["theorem"],
                                                    "statement_identity": occurrence["statement_identity"],
                                                    "registration_module_name": catalog, "registration_module_name_after": leaf}]
        mapping["occurrence_mapping"]["baseline"] = []
        return mapping, catalog, leaf

    def companion_reference(self, registration: dict, *, declaration: str = "consumer", repeat: bool = False) -> dict:
        path = registration["owner"].replace(".", "/") + ".lean"
        reference = registration["unit"] + ".Statement"
        command = self.command(path, "def " + declaration + " := " + reference, "context", {"name": declaration})
        source_bytes = self.sources[path].encode("utf-8")
        start = source_bytes.index(reference.encode("utf-8"), command["start"])
        identifier = {"name": registration["unit"], "start": start, "end": start + len(reference.encode("utf-8")), "text": reference}
        command["companion_identifiers"] = [identifier]
        self.raw.setdefault("companion_bindings", []).append({"path": path, "start": identifier["start"], "end": identifier["end"], "name": registration["unit"]})
        companion = {"owner": registration["owner"], "name": registration["unit"], "level_params": registration["level_params"],
                     "type": {"text": "Synthetic.Unit", "printed": True}, "body": {"text": "Synthetic.originalUnit", "printed": True}}
        if not repeat:
            self.raw.setdefault("companions", []).append(companion)
        return companion

    def specialize(self, row: dict, slot: str, identifier: str, levels: list[str], *, occurrence: int = 0) -> dict:
        path = row["owner"].replace(".", "/") + ".lean"
        file = next(file for file in self.syntax["files"] if file["path"] == path)
        kind = "template" if "name" in row else "registration"
        command = [command for command in file["commands"] if command["kind"] == kind][row["source_index"]]
        span = command["slots"][slot]
        content, needle = span["text"].encode("utf-8"), identifier.encode("utf-8")
        position = content.index(needle)
        for _ in range(occurrence):
            position = content.index(needle, position + len(needle))
        start, end = span["start"] + position, span["start"] + position + len(needle)
        head = identifier.split(".{", 1)[0]
        span.setdefault("identifiers", []).append({"start": start, "end": end, "text": identifier,
                                                   "head_text": head, "name_components": head.split("."),
                                                   "explicit_universes": ".{" in identifier})
        entry = {"start": start, "end": end, "text": identifier,
                 "term": head + (".{" + ", ".join(levels) + "}" if levels else ""),
                 "levels": levels, "level_params": levels}
        row.setdefault("source_specializations", {}).setdefault(slot, []).append(entry)
        return entry


class GeneratorTests(unittest.TestCase):
    def assert_failure_writes_nothing(self, fixture: Fixture, code: str) -> None:
        result = fixture.generator().plan()
        self.assertIn(code, {failure.code for failure in result.failures}, [failure.as_dict() for failure in result.failures])
        self.assertEqual(result.files, [], "failure plans must not expose partial generated files")
        output = fixture.root / "output path"
        with self.assertRaises(GeneratorFailure):
            fixture.generator().write(result, output)
        self.assertFalse(output.exists())

    def test_missing_compiled_input_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.raw["registrations"] = []
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "missing_compiled_input")

    def test_snapshot_disagrees_with_source_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.save()
            (fixture.root / "Reg/D5/Sample.lean").write_text("-- changed\n" + fixture.sources["Reg/D5/Sample.lean"], encoding="utf-8")
            self.assert_failure_writes_nothing(fixture, "source_snapshot_mismatch")

    def test_unknown_syntax_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.command("Reg/D5/Sample.lean", "register_information_new unknown", "unsupported", {"theorem": "unknown"})
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "unknown_syntax")

    def test_raw_input_snapshot_is_authority_without_report(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [failure.as_dict() for failure in result.failures])
            self.assertEqual(len(result.registrations), 1)
            self.assertEqual(result.registrations[0].snapshot["statement_identity"], "identity-from-compiled-input")
            self.assertEqual(len(result.files), 1)

    def test_duplicate_compiled_input_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            fixture.raw["registrations"].append(copy.deepcopy(row))
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "duplicate")

    def test_extra_compiled_input_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            extra = copy.deepcopy(row)
            extra.update(theorem="D5.Sample.extra", source_index=1, unit="extra.unit")
            fixture.raw["registrations"].append(extra)
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "extra_compiled_input")

    def test_generated_declaration_name_collision_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.command("Reg/D5/Sample.lean", "def registration_1 := 2", "context", {"name": "registration_1"})
            fixture.registration()
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "name_collision")

    def test_root_owner_mismatch_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping = fixture.root_catalog()
            mapping["root_id_after"] = "Reg.Catalogs.Wrong.RootCatalog"
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "wrong_root_owner")

    def test_destination_collision_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            first = fixture.root_catalog("Reg/Catalogs/One.lean")
            second = fixture.root_catalog("Reg/Catalogs/Two.lean")
            second.update(destination_path=first["destination_path"], destination_module=first["destination_module"], root_id_after=first["root_id_after"])
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "mapping_collision")

    def test_compiled_source_text_mismatch_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.save()
            fixture.raw["registrations"][0]["source_text"] += "-- stale\n"
            fixture.inputs_path.write_text(json.dumps(fixture.raw), encoding="utf-8")
            self.assert_failure_writes_nothing(fixture, "compiled_source_mismatch")

    def test_source_spans_are_utf8_and_ignore_comment_string_keywords(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            prefix = 'import LeanInformationAuditInterface.Syntax\n-- λ readout via escape continues\n/- 嵌套 /- variation -/ sensitivity -/\ndef text := "register_information_theorem in primitives"\n'
            fixture.source("Reg/D5/Sample.lean", prefix)
            readout = 'Template.realize (fun x => (let s := "escape from variation"; (x, (s, "λ"))))'
            fixture.registration(readout=readout)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertEqual(len(result.registrations), 1)
            self.assertEqual(result.registrations[0].readout, readout)
            self.assertIn(prefix, result.files[0].text)
            self.assertIn(readout, result.files[0].text)

    def test_replace_spans_uses_utf8_bytes_without_corrupting_surroundings(self) -> None:
        text = "-- αβ\nregistration λ\n-- 後\n"
        start = len("-- αβ\n".encode("utf-8"))
        end = start + len("registration λ".encode("utf-8"))
        self.assertEqual(replace_spans(text, [(start, end, "converted")]), "-- αβ\nconverted\n-- 後\n")

    def test_all_registration_variants_keep_math_and_lower_to_contract(self) -> None:
        for variant, constructor in (("legacy", ".legacy"), ("forward", ".forward"), ("witness", ".witness"), ("source", ".source"), ("finite-source", ".legacy"), ("occurrence", ".legacy")):
            with self.subTest(variant=variant), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(variant=variant)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                self.assertEqual(len(result.registrations), 1)
                rendered = result.files[0].text
                self.assertIn(constructor, rendered)
                self.assertIn("Template.realize x", rendered)
                self.assertIn(row["unit"], rendered)
                self.assertIn(row["realization"], rendered)
                self.assertNotIn("targetName :=", rendered)
                if variant in {"legacy", "forward", "witness", "occurrence"}:
                    self.assertIn("⟨(bridge)⟩", rendered)
                    self.assertNotIn("Iff.rfl", rendered)
                if variant == "finite-source":
                    self.assertIn("familyRecord", rendered)
                    self.assertIn("finiteBridge", rendered)
                    self.assertIn("varying", rendered)
                    self.assertIn("sensitive", rendered)

    def test_continuation_absent_unknown_and_evidence_remain_distinct(self) -> None:
        for value, expected in ((None, ".absent"), ("open", ".unknown"), ("residualEvidence", ".evidence")):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration(continuation=value)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                self.assertIn("continuation := " + expected, result.files[0].text)
                if value == "residualEvidence":
                    self.assertIn(value, result.files[0].text)

    def test_inline_bridge_is_materialized_with_original_proof(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(inline=True)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertIn("theorem _root_." + row["realization"], result.files[0].text)
            self.assertIn("by exact originalBridge", result.files[0].text)

    def test_same_theorem_multiple_occurrences_are_not_merged(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration(variant="occurrence", occurrence=1)
            fixture.registration(variant="occurrence", occurrence=2)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertEqual(len(result.registrations), 2)
            self.assertEqual(result.files[0].text.count("Contract.Registration."), 2)
            for value in ("objectArena1", "objectArena2", "catalog1", "catalog2"):
                self.assertIn(value, result.files[0].text)

    def test_private_quoted_names_and_multiple_universes_are_preserved(self) -> None:
        for theorem in ("_private.D5.Sample.0.claim", "D5.Sample.«claim with space.λ»"):
            with self.subTest(theorem=theorem), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(theorem="privateSourceClaim" if theorem.startswith("_private.") else theorem)
                row["level_params"] = ["u", "v"]
                if theorem.startswith("_private."):
                    row["theorem"] = theorem
                    row["unit"] = theorem + ".__unit"
                    row["realization"] = theorem + ".__realization"
                    components = ["_private", "D5", "Sample", 0, "claim"]
                    row["name_components"] = {"theorem": components, "unit": components + ["__unit"], "realization": components + ["__realization"]}
                    row["target_term"] = {"text": "@privateSourceClaim.{u, v}", "printed": True, "level_params": ["u", "v"]}
                else:
                    row["name_components"] = {"theorem": ["D5", "Sample", "claim with space.λ"]}
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                if theorem.startswith("_private."):
                    self.assertIn("@privateSourceClaim.{u, v}", result.files[0].text)
                    self.assertIn("Lean.Name.num", result.files[0].text)
                    self.assertNotIn("`_private.D5.Sample.0.claim", result.files[0].text)
                else:
                    self.assertIn(theorem, result.files[0].text)
                self.assertIn(".{u, v}", result.files[0].text)

    def test_options_are_captured_typed_sorted_and_not_reconstructed_from_source(self) -> None:
        values = [{"name": "scoped.string", "type": "string", "value": "name-like `x λ"}, {"name": "inherited.nat", "type": "nat", "value": 42}, {"name": "a.bool", "type": "bool", "value": False}, {"name": "a.name", "type": "name", "value": "Synthetic.«with space»"}, {"name": "a.int", "type": "int", "value": -7}]
        rendered = options_literal(values)
        self.assertLess(rendered.index("`a.bool"), rendered.index("`scoped.string"))
        for fragment in (".nat 42", ".bool false", '.string "name-like `x λ"', ".name `Synthetic.«with space»", ".int (-7)"):
            self.assertIn(fragment, rendered)
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.source("Reg/D5/Sample.lean", "import LeanInformationAuditInterface.Syntax\nset_option maxRecDepth 1\n")
            fixture.registration(options=values)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertIn("options := " + rendered, result.files[0].text)
            self.assertNotIn("name := `maxRecDepth", result.files[0].text)

    def test_reference_source_selection_is_expanded_and_arrays_remain_ordered(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(variant="source")
            row["source_selection"]["definition"] = {"owner": "D5.Sample", "name": "D5.Sample.namedClaim", "path": ["arg"]}
            row["source_selection"]["readouts"].append({"path": ["domain"], "stateBinder": 3, "functionOperand": True, "stateOperand": ["body", "arg"], "booleanPredicate": True})
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertNotIn("some selectedSource", rendered)
            self.assertIn("coordinates := #[2, 7]", rendered)
            self.assertIn("namedClaim", rendered)
            self.assertLess(rendered.index('path := #["body", "arg"]'), rendered.index('path := #["domain"]'))
            self.assertIn("booleanPredicate := true", rendered)

    def test_simple_and_constructor_templates_use_compiled_version_and_order(self) -> None:
        for constructors in (False, True):
            with self.subTest(constructors=constructors), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.template(constructors=constructors)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                self.assertIn("Contract.TemplateEnrollment", result.files[0].text)
                if constructors:
                    self.assertIn("version := 7", result.files[0].text)
                    self.assertLess(result.files[0].text.index("SyntheticTemplate.second"), result.files[0].text.index("SyntheticTemplate.first"))

    def test_three_root_entry_forms_expand_same_ordered_input(self) -> None:
        for entry in ("root-literal", "root-snapshot", "root-reference"):
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                rows = [{"root_id": "Reg.D5.Sample", "object_arena": "arena", "theorem": "D5.Sample." + value,
                         "statement_identity": "compiled-" + value, "registration_module": "Reg.D5.Sample", "captured_statement": {"text": "True", "printed": True, "level_params": []}} for value in ("z", "a")]
                mapping = fixture.root_catalog(entry=entry, rows=rows)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                rendered = next(item.text for item in result.files if item.kind == "root")
                self.assertIn("rootId := `" + mapping["destination_module"], rendered)
                self.assertIn("registrationModuleName := `Reg.D5.Sample", rendered)
                self.assertLess(rendered.index("D5.Sample.z"), rendered.index("D5.Sample.a"))
                self.assertIn("compiled-z", rendered)
                self.assertIn("compiled-a", rendered)

    def test_seal_captures_options_and_has_new_catalog_owner(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping = fixture.root_catalog(sealed=True)
            fixture.raw["seals"][0]["options"] = [{"name": "seal.flag", "type": "bool", "value": True}]
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = next(item.text for item in result.files if item.kind == "root")
            self.assertIn("Contract.Seal", rendered)
            self.assertIn(".bool true", rendered)
            self.assertEqual(rendered.count("rootId := `" + mapping["destination_module"]), 2)

    def test_72_mirror_splits_and_12_catalog_moves_preserve_leaf_owners(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            for index in range(72):
                path = f"Reg/D5/Synthetic/Leaf{index}.lean"
                fixture.registration(path, theorem=f"D5.Synthetic.claim{index}")
                fixture.root_catalog(path)
            for index in range(12):
                fixture.root_catalog(f"Reg/Catalogs/Synthetic/Catalog{index}.lean")
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertEqual(len(result.roots), 84)
            self.assertEqual(len(result.registrations), 72)
            roots = [item for item in result.files if item.kind == "root"]
            self.assertEqual(len(roots), 84)
            self.assertTrue(all(item.path.startswith("Reg/Catalogs/") for item in roots))
            self.assertFalse(any(item.path.startswith("D5/") for item in result.files))
            for index in range(72):
                leaf = next(item for item in result.files if item.path == f"Reg/D5/Synthetic/Leaf{index}.lean")
                self.assertIn("Contract.Registration", leaf.text)
                self.assertNotIn("RootCatalogs.declare", leaf.text)
                self.assertNotIn("Contract.RootCatalog", leaf.text)
                catalog = next(item for item in roots if item.path == f"Reg/Catalogs/D5/Synthetic/Leaf{index}/RootCatalog.lean")
                self.assertIn(f"registrationModuleName := `Reg.D5.Synthetic.Leaf{index}", catalog.text)
                self.assertNotIn(f"registrationModuleName := `Reg.Catalogs.D5.Synthetic.Leaf{index}", catalog.text)
            relocated = [item for item in roots if not item.path.startswith("Reg/Catalogs/D5/")]
            self.assertTrue(all("registrationModuleName := `Reg.D5.Sample" in item.text for item in relocated))
            # Changing a contributor to the catalog owner is a distinct failure
            # even though the root itself must take that new owner.
            fixture.mapping["modules"][0]["registration_module_name_after"]["expected"][0] = fixture.mapping["modules"][0]["destination_module"]
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "wrong_occurrence_owner")

    def test_input_shuffle_does_not_change_output_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration("Reg/D5/Z.lean", theorem="D5.Z.claim")
            fixture.registration("Reg/D5/A.lean", theorem="D5.A.claim")
            fixture.template()
            fixture.root_catalog("Reg/D5/A.lean")
            fixture.save()
            first = fixture.generator().plan()
            self.assertFalse(first.failures, [f.as_dict() for f in first.failures])
            for values in fixture.raw.values():
                if isinstance(values, list):
                    values.reverse()
            fixture.syntax["files"].reverse()
            fixture.mapping["modules"].reverse()
            fixture.save()
            second = fixture.generator().plan()
            self.assertFalse(second.failures, [f.as_dict() for f in second.failures])
            self.assertEqual([(item.path, item.text) for item in first.files], [(item.path, item.text) for item in second.files])

    def test_different_cwd_and_paths_with_spaces_work_without_shell_configuration(self) -> None:
        with tempfile.TemporaryDirectory(prefix="generator spaced ") as directory:
            fixture = Fixture(Path(directory) / "repo with spaces")
            fixture.registration()
            fixture.save()
            command = [sys.executable, str(PACKAGE_DIR / "generate.py"), "plan", "--repo", str(fixture.root), "--inputs", str(fixture.inputs_path), "--syntax", str(fixture.syntax_path), "--mapping", str(fixture.mapping_path), "--output", str(fixture.root / "output with spaces")]
            environment = {"PATH": os.defpath, "PYTHONPATH": ""}
            result = subprocess.run(command, cwd=directory, env=environment, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            output = fixture.root / "output with spaces" / "rendered" / "Reg/D5/Sample.lean"
            self.assertTrue(output.is_file())

    def test_cli_failure_does_not_create_output_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.raw["registrations"] = []
            fixture.save()
            output = fixture.root / "failure output"
            result = subprocess.run([sys.executable, str(PACKAGE_DIR / "generate.py"), "plan", "--repo", str(fixture.root), "--inputs", str(fixture.inputs_path), "--syntax", str(fixture.syntax_path), "--mapping", str(fixture.mapping_path), "--output", str(output)], text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())


    def test_reconciliation_covers_each_input_once_with_exact_utf8_spans_and_output_names(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            path = "Reg/D5/Sample.lean"
            fixture.source(path, "import LeanInformationAuditInterface.Syntax\n-- 前置 λ\n")
            fixture.registration(path, variant="occurrence", occurrence=1)
            fixture.registration(path, variant="occurrence", occurrence=2)
            fixture.syntax["files"][0]["commands"][1]["namespace"] = "Nested.Qualified"
            fixture.template(constructors=True)
            mapping = fixture.root_catalog(path, sealed=True)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rows = result.audit["reconciliation"]
            self.assertEqual([row["category"] for row in rows], ["registrations", "registrations", "templates", "roots", "seals"])
            keys = [(row["category"], row["owner"], row["source_index"]) for row in rows]
            self.assertEqual(len(keys), len(set(keys)))
            for category in ("registrations", "templates", "roots", "seals"):
                self.assertEqual(sum(row["category"] == category for row in rows), len(fixture.raw[category]))
            for row in rows:
                file = next(file for file in fixture.syntax["files"] if file["path"] == row["source_path"])
                commands = [command for command in file["commands"] if command["kind"] == {"registrations": "registration", "templates": "template", "roots": "root", "seals": "seal"}[row["category"]]]
                command = commands[row["source_index"]]
                self.assertEqual(row["source_span"], {"start": command["start"], "end": command["end"]})
                original = file["source_text"].encode("utf-8")[command["start"]:command["end"]].decode("utf-8")
                self.assertIn(original.splitlines()[0], file["source_text"])
                self.assertTrue(any(output.path == row["output_path"] for output in result.files))
            registrations = rows[:2]
            self.assertEqual([row["identity"]["theorem"] for row in registrations], ["D5.Sample.claim"] * 2)
            self.assertNotEqual(registrations[0]["identity"]["unit"], registrations[1]["identity"]["unit"])
            self.assertEqual([row["output_decl"] for row in registrations], ["Reg.D5.Sample.registration_1", "Nested.Qualified.registration_2"])
            self.assertEqual([row["identity"]["object_arena"] for row in registrations], ["objectArena1", "objectArena2"])
            self.assertEqual(rows[2]["output_decl"], "Reg.Support.Template.enrollment_1")
            self.assertEqual(rows[3]["output_decl"], mapping["destination_module"] + ".rootCatalog")
            self.assertEqual(rows[4]["output_decl"], mapping["destination_module"] + ".seal")
            self.assertEqual(rows[3]["output_path"], rows[4]["output_path"])
            self.assertEqual(rows[3]["output_owner"], mapping["destination_module"])

    def test_reconciliation_preserves_template_and_occurrence_array_order_and_owner_corrections(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping, before, after = fixture.catalog_owner_correction()
            template = fixture.template(constructors=True)
            root = fixture.raw["roots"][0]
            for role in ("expected", "source"):
                second = copy.deepcopy(root[role][0])
                second["statement_identity"] = "a-second"
                root[role].append(second)
                mapping["registration_module_name_after"][role].append(after)
                second_map = copy.deepcopy(mapping["occurrence_mapping"][role][0])
                second_map["statement_identity"] = "a-second"
                mapping["occurrence_mapping"][role].append(second_map)
            root["baseline"] = [copy.deepcopy(root["expected"][1]), copy.deepcopy(root["expected"][0])]
            mapping["registration_module_name_after"]["baseline"] = [after, after]
            mapping["occurrence_mapping"]["baseline"] = list(reversed(copy.deepcopy(mapping["occurrence_mapping"]["expected"])))
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rows = result.audit["reconciliation"]
            template_identity = next(row["identity"] for row in rows if row["category"] == "templates")
            self.assertEqual(template_identity["constructors"], template["constructors"])
            self.assertEqual(template_identity["version"], 7)
            identity = next(row["identity"] for row in rows if row["category"] == "roots")
            self.assertEqual(identity["root_id_before"], before)
            self.assertEqual(identity["root_id_after"], mapping["destination_module"])
            for role in ("expected", "source", "baseline"):
                rows = identity["occurrences"][role]
                self.assertEqual([row["index"] for row in rows], [0, 1])
                self.assertEqual([row["statement_identity"] for row in rows], [row["statement_identity"] for row in root[role]])
                self.assertEqual([row["registration_module_before"] for row in rows], [before, before])
                self.assertEqual([row["registration_module_after"] for row in rows], [after, after])

    def test_reconciliation_is_input_order_independent_and_complete_on_stdout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration("Reg/D5/Z.lean", theorem="D5.Z.claim", occurrence=2)
            fixture.registration("Reg/D5/A.lean", theorem="D5.A.claim", occurrence=1)
            fixture.template()
            fixture.root_catalog("Reg/D5/Z.lean", sealed=True)
            fixture.root_catalog("Reg/D5/A.lean")
            fixture.save()
            expected = fixture.generator().plan().audit["reconciliation"]
            for category in ("registrations", "templates", "roots", "seals"):
                fixture.raw[category].reverse()
            fixture.syntax["files"].reverse()
            fixture.mapping["modules"].reverse()
            fixture.save()
            shuffled = fixture.generator().plan()
            self.assertFalse(shuffled.failures, [f.as_dict() for f in shuffled.failures])
            self.assertEqual(shuffled.audit["reconciliation"], expected)
            output = fixture.root / "stdout output"
            result = subprocess.run([sys.executable, str(PACKAGE_DIR / "generate.py"), "plan", "--repo", str(fixture.root), "--inputs", str(fixture.inputs_path), "--syntax", str(fixture.syntax_path), "--mapping", str(fixture.mapping_path), "--output", str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)["audit"]["reconciliation"], expected)

    def test_failed_plans_expose_empty_reconciliation(self) -> None:
        for failure_stage in ("binding", "rendering", "parser", "invalid_snapshot"):
            with self.subTest(failure_stage=failure_stage), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration()
                if failure_stage == "binding":
                    fixture.raw["registrations"] = []
                elif failure_stage == "rendering":
                    fixture.command("Reg/D5/Sample.lean", "def registration_1 := 2", "context", {"name": "registration_1"})
                elif failure_stage == "parser":
                    fixture.command("Reg/D5/Sample.lean", "register_new unsupported", "unsupported")
                else:
                    fixture.raw["schema"] = "unsupported-raw-schema"
                fixture.save()
                result = fixture.generator().plan()
                self.assertTrue(result.failures)
                self.assertEqual(result.files, [])
                self.assertEqual(result.audit["reconciliation"], [])

    def test_root_scope_enrollments_in_importing_owners_have_distinct_global_names(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.template("Reg/Support/First.lean")
            fixture.source("Reg/Support/Second.lean", "import LeanInformationAuditInterface.Syntax\nimport Reg.Support.First\n\n")
            fixture.template("Reg/Support/Second.lean")
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            declarations = [row["output_decl"] for row in result.audit["reconciliation"]]
            self.assertEqual(declarations, ["Reg.Support.First.enrollment_1", "Reg.Support.Second.enrollment_1"])
            self.assertEqual(len(set(declarations)), 2)
            for output in result.files:
                owner = output.path[:-5].replace("/", ".")
                self.assertIn("noncomputable def _root_." + owner + ".enrollment_1", output.text)
                self.assertNotIn("noncomputable def enrollment_1", output.text)

    def test_ambient_universes_are_not_redeclared_and_target_applications_keep_all_levels(self) -> None:
        for variant in ("native", "inline", "companion", "template"):
            with self.subTest(variant=variant), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                path = "Reg/Support/Ambient.lean"
                fixture.source(path, "import LeanInformationAuditInterface.Syntax\nuniverse u\n\n")
                row = fixture.template(path) if variant == "template" else fixture.registration(path, variant="native" if variant == "native" else "legacy", inline=variant == "inline")
                row["level_params"] = ["u", "v"]
                fixture.syntax["files"][0]["commands"][0]["ambient_universes"] = ["u"]
                if variant == "inline":
                    row["inline_bridge_level_params"] = ["u", "v"]
                if variant == "companion":
                    fixture.companion_reference(row)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                rendered = result.files[0].text
                if variant == "template":
                    self.assertIn("def _root_.Reg.Support.Ambient.enrollment_1.{v}", rendered)
                    self.assertIn("@_root_.SyntheticTemplate.{u, v}", rendered)
                else:
                    self.assertIn("def _root_.Reg.Support.Ambient.registration_1.{v}", rendered)
                    self.assertIn("@_root_.D5.Sample.claim.{u, v}", rendered)
                if variant == "native":
                    self.assertIn("theorem _root_.D5.Sample.claim.{v}", rendered)
                if variant == "inline":
                    self.assertIn("theorem _root_." + row["realization"] + ".{v}", rendered)
                if variant == "companion":
                    self.assertIn("def _root_." + row["unit"] + ".{v}", rendered)
                for declaration in (line for line in rendered.splitlines() if line.startswith(("theorem ", "noncomputable def "))):
                    self.assertNotIn(".{u,", declaration.split(" : ", 1)[0])

    def test_source_specializations_use_ast_spans_keep_utf8_and_ignore_matching_strings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            readout = 'Template.realize (fun λ => ("Template.realize", Template.realize.{old} λ))'
            row = fixture.registration(readout=readout)
            row["extra_level_params"] = ["u", "v"]
            first = fixture.specialize(row, "readout", "Template.realize", ["u", "v"])
            second = fixture.specialize(row, "readout", "Template.realize.{old}", ["u", "v"])
            row["source_specializations"]["readout"].reverse()
            row["type_arg_source_slots"] = [None, None, "readout", None, None, None, None, None]
            row["type_args"][2] = None
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            expected = 'Template.realize.{u, v} (fun λ => ("Template.realize", Template.realize.{u, v} λ))'
            rendered = result.files[0].text
            self.assertIn("readout := some (" + expected + ")", rendered)
            self.assertIn("(type_of% (" + expected + "))", rendered)
            self.assertNotIn(".{old}.{", rendered)
            self.assertEqual(result.audit["source_specializations"][0]["entries"], [first, second])
            printed = [field for item in result.audit["controlled_printing"] for field in item["fields"]]
            self.assertNotIn("readout", printed)
            self.assertNotIn("type_args[2]", printed)

    def test_template_constructor_specializations_preserve_order_and_source_terms(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.template(constructors=True)
            row["extra_level_params"] = ["u"]
            fixture.specialize(row, "constructor_0", "SyntheticTemplate.second", ["u"])
            fixture.specialize(row, "constructor_1", "SyntheticTemplate.first", ["u"])
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertLess(rendered.index("type := (SyntheticTemplate.second.{u})"), rendered.index("type := (SyntheticTemplate.first.{u})"))
            self.assertEqual([row["slot"] for row in result.audit["source_specializations"]], ["constructor_0", "constructor_1"])

    def test_invalid_source_specializations_fail_without_writes_or_partial_audit(self) -> None:
        cases = (("not_map", "invalid_source_specializations"), ("not_entry", "invalid_source_specialization"),
                 ("missing_slot", "invalid_source_specializations"), ("shifted_span", "source_specialization_span_mismatch"),
                 ("wrong_term", "source_specialization_term_mismatch"), ("undeclared_level", "missing_level_params"),
                 ("string_span", "source_specialization_span_mismatch"), ("unclosed_level", "unclosed_expression"),
                 ("overlap", "overlapping_source_specializations"))
        for case, code in cases:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(readout='Template.realize ("Template.realize")')
                row["extra_level_params"] = ["u"]
                entry = fixture.specialize(row, "readout", "Template.realize", ["u"])
                if case == "not_map": row["source_specializations"] = []
                elif case == "not_entry": row["source_specializations"]["readout"] = ["bad"]
                elif case == "missing_slot": row["source_specializations"] = {"missing": [entry]}
                elif case == "shifted_span": entry["start"] += 1
                elif case == "wrong_term": entry["term"] = "Different.realize.{u}"
                elif case == "undeclared_level": entry["level_params"] = ["undeclared"]
                elif case == "string_span":
                    entry["start"] += len('Template.realize ("'.encode())
                    entry["end"] = entry["start"] + len("Template.realize".encode())
                elif case == "unclosed_level": entry.update(levels=["?u.4"], term="Template.realize.{?u.4}", level_params=[])
                else: row["source_specializations"]["readout"].append(copy.deepcopy(entry))
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)
                self.assertEqual(fixture.generator().plan().audit.get("source_specializations", []), [])

    def test_normalized_object_arena_does_not_replace_captured_primitive_bridge_arena(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["bridge_arena_from_source"] = False
            row["bridge_arena"] = {"text": "@PrimitiveArena.{u}", "printed": True, "level_params": ["u"]}
            row["extra_level_params"] = ["u"]
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertIn("realization := .legacy (@PrimitiveArena.{u})", result.files[0].text)
            self.assertIn("arena := ⟨(arena)⟩", result.files[0].text)
            fields = [field for item in result.audit["controlled_printing"] for field in item["fields"]]
            self.assertIn("bridge_arena", fields)

    def test_nested_scope_prefix_applies_to_every_inserted_declaration(self) -> None:
        prefix = "open Classical in\nattribute [local instance] arena.toArena.stateDecidableEq in\n"
        for native in (False, True):
            with self.subTest(native=native), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                path = "Reg/Support/Scoped.lean"
                header = "import LeanInformationAuditInterface.Syntax\n-- λ\n"
                fixture.source(path, header + prefix)
                row = fixture.registration(path, variant="native" if native else "legacy", inline=not native)
                command = fixture.syntax["files"][0]["commands"][0]
                start = len(header.encode("utf-8"))
                middle = start + len("open Classical in\n".encode("utf-8"))
                command["scope_wrappers"] = [{"start": start, "end": middle, "text": "open Classical in\n"},
                                               {"start": middle, "end": command["start"], "text": prefix.split("\n", 1)[1]}]
                fixture.companion_reference(row)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                rendered = result.files[0].text
                self.assertEqual(rendered.count(prefix), 3)
                self.assertIn(prefix + "theorem _root_." + (row["theorem"] if native else row["realization"]), rendered)
                self.assertIn(prefix + "noncomputable def _root_." + row["unit"], rendered)
                self.assertIn(prefix + "noncomputable def _root_.Reg.Support.Scoped.registration_1", rendered)
                self.assertIn("\ndef consumer := " + row["unit"] + ".Statement\n", rendered)

    def test_removed_scoped_root_and_seal_leave_no_dangling_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            path = "Reg/Catalogs/Scoped.lean"
            header, prefix = "import LeanInformationAuditInterface.Syntax\n\n", "open Classical in\n"
            fixture.source(path, header + prefix)
            fixture.root_catalog(path, sealed=True)
            root, seal = fixture.syntax["files"][0]["commands"]
            root["scope_wrappers"] = [{"start": len(header.encode()), "end": root["start"], "text": prefix}]
            old_seal_start = seal["start"]
            source = fixture.sources[path].encode("utf-8")
            fixture.sources[path] = (source[:old_seal_start] + prefix.encode() + source[old_seal_start:]).decode("utf-8")
            seal["start"] += len(prefix.encode())
            seal["end"] += len(prefix.encode())
            seal["scope_wrappers"] = [{"start": old_seal_start, "end": seal["start"], "text": prefix}]
            fixture.command(path, "def kept := True", "context", {"name": "kept"})
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            leaf = next(file for file in result.files if file.path == path)
            self.assertNotIn(prefix, leaf.text)
            self.assertIn("def kept := True", leaf.text)
            self.assertEqual(len(result.audit["reconciliation"]), 2)

    def test_invalid_scoped_prefix_metadata_fails_without_writes(self) -> None:
        for case, code in (("not_array", "invalid_scope_wrapper"), ("not_object", "invalid_scope_wrapper"),
                           ("after_command", "invalid_scope_wrapper"), ("wrong_text", "scope_wrapper_source_mismatch")):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                path = "Reg/Support/Scoped.lean"
                header, prefix = "import LeanInformationAuditInterface.Syntax\n", "open Classical in\n"
                fixture.source(path, header + prefix)
                fixture.registration(path)
                command = fixture.syntax["files"][0]["commands"][0]
                wrapper = {"start": len(header.encode()), "end": command["start"], "text": prefix}
                if case == "not_array": command["scope_wrappers"] = "bad"
                elif case == "not_object": command["scope_wrappers"] = ["bad"]
                else:
                    command["scope_wrappers"] = [wrapper]
                    if case == "after_command": wrapper["end"] += 1
                    else: wrapper["text"] = "different in\n"
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_invalid_ambient_universe_metadata_fails_without_writes(self) -> None:
        for levels in ("u", ["u", "u"], [""], [1]):
            with self.subTest(levels=levels), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration()
                fixture.syntax["files"][0]["commands"][0]["ambient_universes"] = levels
                fixture.save()
                self.assert_failure_writes_nothing(fixture, "invalid_ambient_universes")

    def test_private_template_source_specialization_adds_universe_application_once(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.template()
            row.update(name="_private.Reg.Template.0.template", level_params=["u", "v"], template_term=None,
                       name_components={"name": ["_private", "Reg", "Template", 0, "template"]})
            fixture.specialize(row, "name", "SyntheticTemplate", ["u", "v"])
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertIn("(@SyntheticTemplate.{u, v})", result.files[0].text)
            self.assertNotIn(".{u, v}.{u, v}", result.files[0].text)
            self.assertEqual(result.audit["source_specializations"][0]["slot"], "name")


if __name__ == "__main__":
    unittest.main()
