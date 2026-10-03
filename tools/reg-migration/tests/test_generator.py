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
            fixture.registration(inline=True)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertIn("theorem __p2b_inline_bridge_1", result.files[0].text)
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
                row = fixture.registration(theorem=theorem)
                row["level_params"] = ["u", "v"]
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
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

    def test_missing_universe_material_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            del row["type_args"]
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "missing_material")

    def test_uncontrolled_and_unclosed_fallbacks_fail_without_writes(self) -> None:
        for value, code in (("actual", "uncontrolled_expression"), ({"text": "?m.17", "printed": True}, "unclosed_expression"), ({"text": "actual", "printed": True, "has_fvars": True}, "unclosed_expression")):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                row["actual"] = value
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_source_math_wins_over_printed_terms_and_fallbacks_are_audited(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["supplied_primitives"] = {"text": "Synthetic.printedDifferentPrimitives", "printed": True}
            row["readout"] = {"text": "Synthetic.printedDifferentReadout", "printed": True}
            row["actual"] = {"text": "@Synthetic.actual.{0}", "printed": True, "level_params": []}
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertIn("actual.toPrimitiveBundle", rendered)
            self.assertIn("Template.realize x", rendered)
            self.assertNotIn("printedDifferent", rendered)
            self.assertIn("@Synthetic.actual.{0}", rendered)
            printed = next(item for item in result.audit["controlled_printing"] if item["theorem"] == row["theorem"])
            self.assertIn("actual", printed["fields"])
            self.assertNotIn("supplied_primitives", printed["fields"])
            self.assertNotIn("readout", printed["fields"])

    def test_native_theorem_full_telescope_and_proof_remain_in_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(variant="native")
            row["level_params"] = ["u", "v"]
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertIn("theorem D5.Sample.claim.{u, v} : ∀ (α : Type u) (β : Type v), True := by intros; trivial", rendered)
            self.assertIn("generated := true", rendered)

    def test_repeated_write_preserves_bytes_and_file_mtimes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.save()
            generator = fixture.generator()
            first = generator.plan()
            second = generator.plan()
            self.assertFalse(first.failures, [f.as_dict() for f in first.failures])
            self.assertFalse(second.failures, [f.as_dict() for f in second.failures])
            self.assertEqual([(item.path, item.text) for item in first.files], [(item.path, item.text) for item in second.files])
            output = fixture.root / "rendered"
            generator.write(first, output)
            before = {path.relative_to(output).as_posix(): (path.read_bytes(), path.stat().st_mtime_ns) for path in output.rglob("*") if path.is_file()}
            generator.write(second, output)
            after = {path.relative_to(output).as_posix(): (path.read_bytes(), path.stat().st_mtime_ns) for path in output.rglob("*") if path.is_file()}
            self.assertEqual(before, after)

    def test_migrated_tree_second_plan_has_zero_changes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.root_catalog()
            fixture.save()
            generator = fixture.generator()
            first = generator.plan()
            self.assertFalse(first.failures, [f.as_dict() for f in first.failures])
            generator.write(first, fixture.root)
            second = generator.plan()
            self.assertFalse(second.failures, [f.as_dict() for f in second.failures])
            self.assertEqual(second.audit["changed_files"], 0)
            self.assertEqual(second.files, [])

    def test_input_sha_is_checked_before_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            fixture.save()
            result = fixture.generator().plan("0" * 64)
            self.assertEqual({item.code for item in result.failures}, {"snapshot_sha_mismatch"})
            self.assertEqual(result.files, [])

    def test_invalid_utf8_slot_and_unknown_variant_fail_without_writes(self) -> None:
        for malformed, code in (("utf8", "invalid_utf8_span"), ("variant", "unknown_registration_shape")):
            with self.subTest(malformed=malformed), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration(readout="Template.realize λ")
                command = fixture.syntax["files"][0]["commands"][0]
                if malformed == "utf8":
                    command["slots"]["readout"]["end"] -= 1
                else:
                    command["variant"] = "future-variant"
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_wrong_registration_owner_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["registration_module"] = "Reg.Catalogs.D5.Sample.RootCatalog"
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "wrong_registration_owner")

    def test_options_reject_duplicate_name_wrong_type_and_negative_nat(self) -> None:
        for options, code in (([{"name": "x", "type": "nat", "value": 1}, {"name": "x", "type": "nat", "value": 2}], "duplicate_option"), ([{"name": "x", "type": "nat", "value": -1}], "unsupported_option_type"), ([{"name": "x", "type": "bool", "value": 1}], "unsupported_option_type")):
            with self.subTest(options=options), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration(options=options)
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)


if __name__ == "__main__":
    unittest.main()
