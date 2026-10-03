from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from test_generator import Fixture, Generator, GeneratorFailure, options_literal, replace_spans, ROOT, PACKAGE_DIR


class GeneratorMaterialTests(unittest.TestCase):
    def universe_specialization(self, fixture: Fixture, row: dict, anchor: str, captured: str) -> dict:
        path = row["owner"].replace(".", "/") + ".lean"
        file = next(file for file in fixture.syntax["files"] if file["path"] == path)
        command = [command for command in file["commands"] if command["kind"] == "registration"][row["source_index"]]
        span = command["slots"]["readout"]
        raw, marker = span["text"].encode("utf-8"), anchor.encode("utf-8")
        offset = raw.index(marker) + len(marker) - 1
        start = span["start"] + offset
        span.setdefault("universe_occurrences", []).append({"start": start, "end": start + 1,
                                                            "text": "u", "name_components": ["u"]})
        entry = {"kind": "universe-parameter", "start": start, "end": start + 1,
                 "text": "u", "term": "(" + captured + ")", "levels": [captured],
                 "level_params": [captured]}
        row.setdefault("source_specializations", {}).setdefault("readout", []).append(entry)
        return entry

    def assert_failure_writes_nothing(self, fixture: Fixture, code: str) -> None:
        result = fixture.generator().plan()
        self.assertIn(code, {failure.code for failure in result.failures}, [failure.as_dict() for failure in result.failures])
        self.assertEqual(result.files, [], "failure plans must not expose partial generated files")
        output = fixture.root / "output path"
        with self.assertRaises(GeneratorFailure):
            fixture.generator().write(result, output)
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
            self.assertIn("theorem _root_.D5.Sample.claim.{u, v} : ∀ (α : Type u) (β : Type v), True := by intros; trivial", rendered)
            self.assertIn("generated := true", rendered)
            realization = next(line for line in rendered.splitlines() if line.startswith("  realization := "))
            self.assertTrue(realization.endswith(" ⟨(⟨Iff.rfl⟩)⟩,"), realization)
            self.assertFalse(realization.endswith(" ⟨(Iff.rfl)⟩,"), realization)
            self.assertFalse(realization.endswith(" ⟨Iff.rfl⟩,"), realization)

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

    def test_authorized_catalog_owner_correction_uses_matching_registration_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping, before, after = fixture.catalog_owner_correction()
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = next(item.text for item in result.files if item.kind == "root")
            self.assertIn("rootId := `" + mapping["destination_module"], rendered)
            self.assertEqual(rendered.count("registrationModuleName := `" + after), 2)
            self.assertNotIn("registrationModuleName := `" + before, rendered)
            self.assertEqual(fixture.raw["roots"][0]["expected"][0]["registration_module"], before)
            self.assertEqual(result.roots[0].expected[0]["registration_module"], after)

    def test_catalog_owner_correction_rejects_wrong_before_after_and_missing_leaf(self) -> None:
        for field in ("before", "after", "missing_leaf"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                mapping, before, after = fixture.catalog_owner_correction()
                if field == "before":
                    mapping["occurrence_mapping"]["expected"][0]["registration_module_name"] = "Reg.Catalogs.Different"
                elif field == "after":
                    mapping["occurrence_mapping"]["expected"][0]["registration_module_name_after"] = "Reg.D5.Different"
                else:
                    for role in ("expected", "source"):
                        mapping["registration_module_name_after"][role] = ["Reg.D5.MissingContributor"]
                        mapping["occurrence_mapping"][role][0]["registration_module_name_after"] = "Reg.D5.MissingContributor"
                fixture.save()
                self.assert_failure_writes_nothing(fixture, "wrong_occurrence_owner")

    def test_catalog_owner_correction_requires_explicit_occurrence_mapping(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping, before, after = fixture.catalog_owner_correction()
            del mapping["occurrence_mapping"]
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "unauthorized_owner_correction")

    def test_referenced_companion_is_preserved_by_one_ordinary_definition(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            first = fixture.registration()
            first["level_params"] = ["u", "v"]
            fixture.companion_reference(first)
            second = fixture.registration(occurrence=1)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            helper = "noncomputable def _root_." + first["unit"] + ".{u, v} : Synthetic.Unit := Synthetic.originalUnit"
            self.assertEqual(rendered.count(helper), 1)
            self.assertIn("def consumer := " + first["unit"] + ".Statement", rendered)
            self.assertNotIn("noncomputable def _root_." + second["unit"], rendered)
            self.assertLess(rendered.index(helper), rendered.index("noncomputable def _root_.Reg.D5.Sample.registration_1"))
            self.assertEqual(result.audit["companion_helpers"], 1)
            self.assertEqual(result.audit["companion_consumers"], 1)
            printed = next(item["fields"] for item in result.audit["controlled_printing"] if "companion:" + first["unit"] + ":body" in item["fields"])
            self.assertIn("companion:" + first["unit"] + ":type", printed)

    def test_multiple_companion_references_do_not_duplicate_helper_or_merge_occurrences(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            first = fixture.registration(variant="occurrence", occurrence=1)
            second = fixture.registration(variant="occurrence", occurrence=2)
            second["unit"] = first["unit"]
            fixture.companion_reference(first, declaration="firstConsumer")
            fixture.companion_reference(second, declaration="secondConsumer", repeat=True)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertEqual(rendered.count("noncomputable def _root_." + first["unit"]), 1)
            self.assertEqual(rendered.count("Contract.Registration."), 2)
            self.assertIn("def firstConsumer := " + first["unit"] + ".Statement", rendered)
            self.assertIn("def secondConsumer := " + first["unit"] + ".Statement", rendered)
            self.assertEqual(result.audit["companion_helpers"], 1)
            self.assertEqual(result.audit["companion_consumers"], 2)

    def test_missing_companion_or_compiled_binding_fails_without_writes(self) -> None:
        for field in ("companions", "companion_bindings"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                fixture.companion_reference(row)
                fixture.raw[field] = []
                fixture.save()
                self.assert_failure_writes_nothing(fixture, "missing_compiled_companion")

    def test_duplicate_companion_and_binding_fail_without_writes(self) -> None:
        for field, code in (("companions", "duplicate_companion"), ("companion_bindings", "duplicate_companion_binding")):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                fixture.companion_reference(row)
                fixture.raw[field].append(copy.deepcopy(fixture.raw[field][0]))
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_companion_body_missing_uncontrolled_or_open_fails_without_writes(self) -> None:
        for body, code in ((None, "missing_companion_term"), ("Synthetic.originalUnit", "uncontrolled_expression"), ({"text": "?m.19", "printed": True}, "unclosed_expression"), ({"text": "Synthetic.originalUnit", "printed": True, "has_fvars": True}, "unclosed_expression")):
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                companion = fixture.companion_reference(row)
                companion["body"] = body
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_companion_name_collision_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            fixture.companion_reference(row)
            command = fixture.command("Reg/D5/Sample.lean", "def existingHelper := 1", "context", {"name": "existingHelper"})
            command["declared_names"] = [row["unit"]]
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "name_collision")

    def test_unreferenced_companion_and_extra_binding_fail_without_writes(self) -> None:
        for field, code in (("companions", "unreferenced_companion"), ("companion_bindings", "extra_companion_binding")):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                fixture.companion_reference(row)
                if field == "companions":
                    second = fixture.registration(occurrence=1)
                    extra = copy.deepcopy(fixture.raw["companions"][0])
                    extra["name"] = second["unit"]
                    fixture.raw["companions"].append(extra)
                else:
                    extra = copy.deepcopy(fixture.raw["companion_bindings"][0])
                    extra["start"] += 1
                    fixture.raw["companion_bindings"].append(extra)
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_constructor_source_slots_replace_missing_printed_constructor_types(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.template(constructors=True)
            row["constructor_types"] = {name: None for name in row["constructors"]}
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            for name in row["constructors"]:
                self.assertIn("name := `" + name + ", type := (" + name + ")", rendered)
            printed = [field for item in result.audit["controlled_printing"] for field in item["fields"]]
            self.assertFalse(any(field.startswith("constructor_types:") for field in printed))

    def test_extra_universes_are_preserved_without_changing_target_universes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row.update(level_params=["u"], extra_level_params=["v"])
            row["actual"] = {"text": "@Synthetic.actual.{v}", "printed": True, "level_params": ["v"]}
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertIn("def _root_.Reg.D5.Sample.registration_1.{u, v}", rendered)
            self.assertIn("@_root_.D5.Sample.claim.{u}", rendered)
            self.assertNotIn("@_root_.D5.Sample.claim.{u, v}", rendered)
            self.assertIn("@Synthetic.actual.{v}", rendered)

    def test_invalid_duplicate_or_overlapping_extra_universes_fail_without_writes(self) -> None:
        for values, code in (("v", "invalid_level_params"), ([""], "invalid_level_params"), ([3], "invalid_level_params"), (["v", "v"], "duplicate_level_params"), (["u"], "duplicate_level_params")):
            with self.subTest(values=values), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                row.update(level_params=["u"], extra_level_params=values)
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_undeclared_printed_expression_universe_fails_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["actual"] = {"text": "@Synthetic.actual.{w}", "printed": True, "level_params": ["w"]}
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "missing_level_params")

    def test_companion_dependency_closure_is_ordered_and_input_shuffle_is_irrelevant(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            unit = fixture.companion_reference(row)
            primitive_name = row["theorem"] + ".__primitive_realization"
            primitive = {"owner": row["owner"], "name": primitive_name, "anchor_unit": row["unit"], "level_params": [],
                         "type": {"text": "Synthetic.Primitive", "printed": True}, "body": {"text": "Synthetic.actual", "printed": True}, "companion_dependencies": []}
            unit.update(companion_dependencies=[primitive_name], anchor_unit=row["unit"], body={"text": "Synthetic.unitFromPrimitive " + primitive_name, "printed": True})
            fixture.raw["companions"].append(primitive)
            fixture.save()
            first = fixture.generator().plan()
            self.assertFalse(first.failures, [f.as_dict() for f in first.failures])
            rendered = first.files[0].text
            self.assertLess(rendered.index("def _root_." + primitive_name), rendered.index("def _root_." + row["unit"]))
            self.assertEqual(first.audit["companion_helpers"], 2)
            fixture.raw["companions"].reverse()
            fixture.save()
            second = fixture.generator().plan()
            self.assertFalse(second.failures, [f.as_dict() for f in second.failures])
            self.assertEqual([(item.path, item.text) for item in first.files], [(item.path, item.text) for item in second.files])

    def test_companion_dependency_cycle_and_missing_dependency_fail_without_writes(self) -> None:
        for malformed, code in (("cycle", "companion_cycle"), ("missing", "missing_companion_dependency")):
            with self.subTest(malformed=malformed), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                unit = fixture.companion_reference(row)
                dependency_name = row["theorem"] + ".__primitive_realization"
                unit["companion_dependencies"] = [dependency_name]
                if malformed == "cycle":
                    fixture.raw["companions"].append({"owner": row["owner"], "name": dependency_name, "anchor_unit": row["unit"], "level_params": [],
                                                      "type": {"text": "Synthetic.Primitive", "printed": True}, "body": {"text": "Synthetic.actual", "printed": True},
                                                      "companion_dependencies": [row["unit"]]})
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_inline_companion_reference_reuses_original_source_bridge_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(inline=True)
            fixture.companion_reference(row)
            reference = row["realization"]
            command = fixture.command("Reg/D5/Sample.lean", "def bridgeConsumer := " + reference, "context", {"name": "bridgeConsumer"})
            start = fixture.sources["Reg/D5/Sample.lean"].encode("utf-8").index(reference.encode("utf-8"), command["start"])
            command["companion_identifiers"] = [{"name": reference, "start": start, "end": start + len(reference.encode("utf-8")), "text": reference}]
            fixture.raw["companion_bindings"].append({"path": "Reg/D5/Sample.lean", "start": start, "end": start + len(reference.encode("utf-8")), "name": reference})
            fixture.raw["companions"].append({"owner": row["owner"], "name": reference, "anchor_unit": row["unit"], "level_params": [],
                                               "type": {"text": "Synthetic.Bridge", "printed": True}, "body": {"text": "originalBridge", "printed": True}})
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertEqual(rendered.count("theorem _root_." + reference), 1)
            self.assertNotIn("noncomputable def _root_." + reference, rendered)
            self.assertIn("by exact originalBridge", rendered)
            self.assertIn("def bridgeConsumer := " + reference, rendered)

    def test_inline_bridge_source_universes_and_aligned_application_universes_remain_distinct(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(inline=True)
            row.update(level_params=["u"], inline_bridge_level_params=["v"],
                       inline_bridge_type={"text": "Synthetic.Bridge.{v}", "printed": True, "level_params": ["v"]},
                       inline_bridge_term={"text": "@_root_." + row["realization"] + ".{u}", "printed": True, "level_params": ["u"]})
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertIn("theorem _root_." + row["realization"] + ".{v} : Synthetic.Bridge.{v}", rendered)
            self.assertIn("def _root_.Reg.D5.Sample.registration_1.{u}", rendered)
            self.assertIn("@_root_." + row["realization"] + ".{u}", rendered)
            self.assertNotIn("def _root_.Reg.D5.Sample.registration_1.{u, v}", rendered)

    def test_inline_bridge_aligned_term_requires_declared_target_universes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(inline=True)
            row.update(level_params=["u"], inline_bridge_level_params=["v"],
                       inline_bridge_type={"text": "Synthetic.Bridge.{v}", "printed": True, "level_params": ["v"]},
                       inline_bridge_term={"text": "@_root_." + row["realization"] + ".{v}", "printed": True, "level_params": ["v"]})
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "missing_level_params")

    def test_structured_name_literals_distinguish_numeric_and_string_components(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["unit"] = "_private.Reg.Example.0.unit"
            row["realization"] = "_private.Reg.Example.0.bridge"
            row["name_components"] = {"unit": ["_private", "Reg", "Example", 0, "unit"],
                                      "realization": ["_private", "Reg", "Example", "0", "bridge"]}
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            unit_line = next(line for line in rendered.splitlines() if "unitName :=" in line)
            bridge_line = next(line for line in rendered.splitlines() if "realizationName :=" in line)
            self.assertIn('Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "Example") 0', unit_line)
            self.assertNotIn('"0"', unit_line)
            self.assertIn('"0"', bridge_line)
            self.assertNotIn("Lean.Name.num", bridge_line)
            self.assertNotIn("`_private.", rendered)

    def test_missing_invalid_private_name_components_and_target_terms_fail_without_writes(self) -> None:
        for malformed, code in (("missing_components", "missing_name_components"), ("negative_numeric", "invalid_name_components"), ("boolean_component", "invalid_name_components"), ("missing_target", "missing_private_target_term"), ("uncontrolled_target", "uncontrolled_expression"), ("open_target", "unclosed_expression")):
            with self.subTest(malformed=malformed), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(theorem="privateSourceClaim")
                row["theorem"] = "_private.Reg.Example.0.claim"
                row["name_components"] = {"theorem": ["_private", "Reg", "Example", 0, "claim"]}
                row["target_term"] = {"text": "@privateSourceClaim", "printed": True, "level_params": []}
                if malformed == "missing_components":
                    row["name_components"] = {}
                elif malformed == "negative_numeric":
                    row["name_components"]["theorem"][3] = -1
                elif malformed == "boolean_component":
                    row["name_components"]["theorem"][3] = True
                elif malformed == "missing_target":
                    del row["target_term"]
                elif malformed == "uncontrolled_target":
                    row["target_term"] = "@privateSourceClaim"
                else:
                    row["target_term"]["has_mvars"] = True
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_typed_name_options_preserve_structural_components_and_sort_by_name(self) -> None:
        settings = [{"name": "z.option", "name_components": ["z", "option"], "type": "name", "value": "_private.Reg.Example.0.value", "value_components": ["_private", "Reg", "Example", 0, "value"]},
                    {"name": "a.option", "name_components": ["a", "option"], "type": "name", "value": "Synthetic.«name.with.dot»", "value_components": ["Synthetic", "name.with.dot"]}]
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration(options=settings)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            options = result.registrations[0].options
            self.assertEqual([item["name"] for item in options], ["a.option", "z.option"])
            self.assertEqual(options[1]["value_components"], ["_private", "Reg", "Example", 0, "value"])
            rendered = result.files[0].text
            self.assertIn("Lean.Name.num", rendered)
            self.assertIn('"value"', rendered)
            self.assertIn('Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Synthetic") "name.with.dot"', rendered)
            self.assertNotIn("`_private.", rendered)

    def test_catalog_owner_correction_replaces_original_owner_name_components(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            mapping, before, after = fixture.catalog_owner_correction()
            fixture.raw["registrations"][0]["name_components"] = {"owner": ["Reg", "D5", "Contributor"]}
            for role in ("expected", "source"):
                fixture.raw["roots"][0][role][0]["name_components"] = {"registration_module": ["Reg", "Catalogs", "Collected"]}
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            for role in ("expected", "source"):
                occurrence = getattr(result.roots[0], role)[0]
                self.assertEqual(occurrence["registration_module"], after)
                self.assertEqual(occurrence["name_components"]["registration_module"], ["Reg", "D5", "Contributor"])

    def test_source_backed_type_args_keep_exact_terms_without_printing_audit(self) -> None:
        readout = '(fun λ => Template.realize (λ, "escape from λ")) x /- primitives -/'
        for variant in ("legacy", "occurrence", "source", "finite-source", "native"):
            with self.subTest(variant=variant), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(variant=variant, continuation="residualEvidence", readout=readout)
                slots = fixture.syntax["files"][0]["commands"][0]["slots"]
                sources = ["arena", "object_arena" if variant == "occurrence" else "arena", "readout",
                           "variation" if "variation" in slots else None,
                           "sensitivity" if "sensitivity" in slots else None,
                           "escape_from" if "escape_from" in slots else None,
                           "continuation", "source_record" if "source_record" in slots else None]
                row["type_arg_source_slots"] = sources
                for index, source in enumerate(sources):
                    if source is not None:
                        row["type_args"][index] = None
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                rendered = result.files[0].text
                printed = next(item["fields"] for item in result.audit["controlled_printing"] if item.get("theorem") == row["theorem"])
                self.assertIn("(type_of% (" + readout + "))", rendered)
                for index, source in enumerate(sources):
                    if source is not None:
                        self.assertIn("(type_of% (" + slots[source]["text"] + "))", rendered)
                        self.assertNotIn(f"type_args[{index}]", printed)
                    else:
                        self.assertIn(f"type_args[{index}]", printed)

    def test_malformed_type_arg_source_slots_fail_without_writes(self) -> None:
        for sources in ("readout", [None] * 7, [None, None, "arena"] + [None] * 5,
                        [None, None, 2] + [None] * 5, [None, None, "unknown"] + [None] * 5):
            with self.subTest(sources=sources), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                row["type_arg_source_slots"] = sources
                fixture.save()
                self.assert_failure_writes_nothing(fixture, "invalid_type_arg_source_slots")

    def test_missing_mismatched_and_open_type_arg_sources_fail_without_writes(self) -> None:
        for case, code in (("no_source_record", "missing_type_arg_source"),
                           ("open_continuation", "missing_type_arg_source"),
                           ("nonnull_source_arg", "type_arg_source_mismatch"),
                           ("null_without_source", "missing_type_arg_source")):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                sources = [None] * 8
                if case == "no_source_record":
                    sources[7], row["type_args"][7] = "source_record", None
                elif case == "open_continuation":
                    sources[6], row["type_args"][6] = "continuation", None
                elif case == "nonnull_source_arg":
                    sources[2] = "readout"
                else:
                    row["type_args"][2] = None
                row["type_arg_source_slots"] = sources
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_non_source_type_args_require_closed_declared_controlled_terms(self) -> None:
        for value, code in (("Unit", "uncontrolled_expression"),
                            ({"text": "Unit", "printed": True, "has_fvars": True}, "unclosed_expression"),
                            ({"text": "?m.9", "printed": True}, "unclosed_expression"),
                            ({"text": "Type u", "printed": True, "level_params": ["u"]}, "missing_level_params")):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration()
                row["type_args"][2] = value
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_consumed_root_private_target_is_validated_and_audited(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(theorem="privateSourceClaim")
            row["theorem"] = "_private.D5.Sample.0.claim"
            row["name_components"] = {"theorem": ["_private", "D5", "Sample", 0, "claim"]}
            row["target_term"] = {"text": "@privateSourceClaim", "printed": True, "level_params": []}
            fixture.root_catalog()
            for role in ("expected", "source"):
                occurrence = fixture.raw["roots"][0][role][0]
                occurrence.update(level_params=["u", "v"], name_components=copy.deepcopy(row["name_components"]),
                                  target_term={"text": "@privateSourceClaim.{u, v}", "printed": True, "level_params": ["u", "v"]})
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            root_file = next(file for file in result.files if file.path.endswith("/RootCatalog.lean"))
            self.assertIn("@privateSourceClaim.{u, v}", root_file.text)
            printed = next(item["fields"] for item in result.audit["controlled_printing"] if "root" in item)
            self.assertIn("expected[0].target_term", printed)
            self.assertIn("source[0].target_term", printed)

    def test_root_target_and_statement_fallbacks_fail_closed_without_writes(self) -> None:
        for field, value, code in (("target_term", "@privateSourceClaim", "uncontrolled_expression"),
                                  ("target_term", {"text": "@privateSourceClaim", "printed": True, "has_mvars": True}, "unclosed_expression"),
                                  ("target_term", {"text": "@privateSourceClaim", "printed": True, "has_fvars": True}, "unclosed_expression"),
                                  ("target_term", {"text": "@privateSourceClaim.{u}", "printed": True, "level_params": ["u"]}, "missing_level_params"),
                                  ("captured_statement", {"text": "Sort u", "printed": True, "level_params": ["u"]}, "missing_level_params")):
            with self.subTest(field=field, value=value), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                fixture.registration()
                fixture.root_catalog()
                occurrence = fixture.raw["roots"][0]["expected"][0]
                occurrence["theorem"] = "_private.D5.Sample.0.claim"
                occurrence["name_components"] = {"theorem": ["_private", "D5", "Sample", 0, "claim"]}
                occurrence["target_term"] = {"text": "@privateSourceClaim", "printed": True, "level_params": []}
                occurrence[field] = value
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_private_template_source_name_and_controlled_fallback_are_audited_separately(self) -> None:
        for fallback in (None, {"text": "@privateSourceTemplate.{u}", "printed": True, "level_params": ["u"]}):
            with self.subTest(fallback=fallback), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.template()
                row.update(name="_private.Reg.Template.0.template", level_params=["u"],
                           name_components={"name": ["_private", "Reg", "Template", 0, "template"]}, template_term=fallback)
                fixture.save()
                result = fixture.generator().plan()
                self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
                rendered = result.files[0].text
                self.assertIn("@SyntheticTemplate.{u}" if fallback is None else fallback["text"], rendered)
                fields = [field for item in result.audit["controlled_printing"] for field in item["fields"]]
                self.assertEqual("template_term" in fields, fallback is not None)

    def test_private_template_fallbacks_fail_closed_without_writes(self) -> None:
        for value, code in (("@privateSourceTemplate", "uncontrolled_expression"),
                            ({"text": "@privateSourceTemplate", "printed": True, "has_fvars": True}, "unclosed_expression"),
                            ({"text": "@privateSourceTemplate.{u}", "printed": True, "level_params": ["u"]}, "missing_level_params")):
            with self.subTest(value=value), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.template()
                row.update(name="_private.Reg.Template.0.template",
                           name_components={"name": ["_private", "Reg", "Template", 0, "template"]}, template_term=value)
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_source_target_mismatch_remains_named_compile_blocker_without_changing_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(variant="source")
            row.update(source_target_matches=True,
                       theorem_type={"text": "OriginalClaim", "printed": True, "level_params": []},
                       bridge_type={"text": "SelectedSourceClaim", "printed": True, "level_params": []})
            fixture.save()
            matched = fixture.generator().plan()
            self.assertFalse(matched.failures)
            self.assertEqual(matched.audit["compile_blockers"], [])
            row["source_target_matches"] = False
            fixture.save()
            mismatch = fixture.generator().plan()
            self.assertFalse(mismatch.failures, [f.as_dict() for f in mismatch.failures])
            self.assertEqual([(file.path, file.text) for file in matched.files],
                             [(file.path, file.text) for file in mismatch.files])
            self.assertEqual(mismatch.audit["d5_writes"], 0)
            self.assertEqual(mismatch.audit["compile_blockers"], [{
                "code": "source_target_contract_mismatch", "owner": row["owner"],
                "source_index": row["source_index"], "theorem": row["theorem"],
                "theorem_type": row["theorem_type"], "bridge_type": row["bridge_type"]}])

    def test_compile_blocker_remains_in_zero_write_failure_audit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration(variant="source")
            row["source_target_matches"] = False
            del row["type_args"]
            fixture.save()
            result = fixture.generator().plan()
            self.assertEqual(result.files, [])
            self.assertIn("missing_material", {failure.code for failure in result.failures})
            self.assertEqual(result.audit["compile_blockers"][0]["code"], "source_target_contract_mismatch")
            self.assert_failure_writes_nothing(fixture, "missing_material")

    def test_namespaced_registration_and_template_name_collisions_fail_without_writes(self) -> None:
        for kind, name in (("registration", "registration_1"), ("template", "enrollment_1")):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                path = "Reg/Support/Namespaced.lean"
                fixture.command(path, "namespace SampleNamespace", "context")
                declaration = fixture.command(path, "def " + name + " := 2", "context", {"name": name})
                declaration["declared_names"] = ["SampleNamespace." + name]
                declaration["slots"] = {}
                if kind == "registration":
                    fixture.registration(path)
                else:
                    fixture.template(path)
                fixture.syntax["files"][0]["commands"][-1]["namespace"] = "SampleNamespace"
                fixture.command(path, "end SampleNamespace", "context")
                fixture.save()
                self.assert_failure_writes_nothing(fixture, "name_collision")

    def test_compiled_command_fragment_cannot_bind_full_scoped_option_source(self) -> None:
        for kind in ("registration", "template"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                path = "Reg/Support/ScopedOptions.lean"
                fixture.command(path, "set_option maxRecDepth 2048", "context")
                row = fixture.registration(path) if kind == "registration" else fixture.template(path)
                captured_fragment = row["source_text"]
                fixture.command(path, "set_option pp.universes true in\ndef optionSensitive := True", "context")
                fixture.save()
                self.assertNotEqual(captured_fragment, row["source_text"])
                row["source_text"] = captured_fragment
                fixture.inputs_path.write_text(json.dumps(fixture.raw), encoding="utf-8")
                self.assert_failure_writes_nothing(fixture, "compiled_source_mismatch")

    def test_same_count_missing_and_duplicate_inputs_fail_without_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            first = fixture.registration(theorem="D5.Sample.first")
            fixture.registration(theorem="D5.Sample.second")
            fixture.raw["registrations"][1] = copy.deepcopy(first)
            fixture.save()
            result = fixture.generator().plan()
            self.assertEqual(len(fixture.raw["registrations"]), 2)
            self.assertEqual(result.audit["source_registrations"], 2)
            self.assertIn("duplicate", {failure.code for failure in result.failures})
            self.assertIn("missing_compiled_input", {failure.code for failure in result.failures})
            self.assert_failure_writes_nothing(fixture, "duplicate")

    def test_migrated_source_needs_no_historical_raw_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            path = "Reg/D5/Sample.lean"
            fixture.registration(path)
            fixture.save()
            first = fixture.generator().plan()
            self.assertFalse(first.failures)
            fixture.generator().write(first, fixture.root)
            fixture.sources[path] = (fixture.root / path).read_text(encoding="utf-8")
            fixture.syntax["files"][0]["commands"] = []
            fixture.raw["registrations"] = []
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertEqual(result.audit["changed_files"], 0)
            self.assertEqual(result.files, [])

    def test_mixed_tree_added_source_only_changes_its_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            old_path = "Reg/D5/AlreadyMigrated.lean"
            new_path = "Reg/D5/NewSource.lean"
            fixture.registration(old_path, theorem="D5.AlreadyMigrated.claim")
            fixture.save()
            first = fixture.generator().plan()
            self.assertFalse(first.failures)
            fixture.generator().write(first, fixture.root)
            fixture.sources[old_path] = (fixture.root / old_path).read_text(encoding="utf-8")
            fixture.syntax["files"][0]["commands"] = []
            fixture.raw["registrations"] = []
            fixture.registration(new_path, theorem="D5.NewSource.claim")
            fixture.save()
            before = ((fixture.root / old_path).read_bytes(), (fixture.root / old_path).stat().st_mtime_ns)
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            self.assertEqual([file.path for file in result.files], [new_path])
            fixture.generator().write(result, fixture.root)
            self.assertEqual(before, ((fixture.root / old_path).read_bytes(), (fixture.root / old_path).stat().st_mtime_ns))
            self.assertEqual(result.audit["d5_writes"], 0)

    def test_local_notation_scope_shadowing_and_references_keep_source_context(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            path = "Reg/Support/ScopedNotation.lean"
            outer = 'local notation "view" => Template.realize outer'
            alias = 'local notation "viewAlias" => view'
            inner = 'local notation "view" => Template.realize inner'
            fixture.command(path, "namespace Scope", "context")
            fixture.command(path, outer, "notation")
            fixture.command(path, alias, "notation")
            fixture.registration(path, theorem="D5.Sample.outer", readout="viewAlias")
            fixture.command(path, "section Inner", "context")
            fixture.command(path, inner, "notation")
            fixture.registration(path, theorem="D5.Sample.inner", readout="view")
            fixture.command(path, "end Inner", "context")
            fixture.command(path, "def keptOuter := viewAlias\nend Scope", "context")
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [f.as_dict() for f in result.failures])
            rendered = result.files[0].text
            self.assertEqual(result.audit["notations"], 3)
            self.assertEqual([registration.readout for registration in result.registrations], ["viewAlias", "view"])
            positions = [rendered.index(text) for text in ("namespace Scope", outer, alias, "registration_1",
                                                         "section Inner", inner, "registration_2", "end Inner",
                                                         "def keptOuter := viewAlias", "end Scope")]
            self.assertEqual(positions, sorted(positions))
            self.assertFalse(any(file.path.startswith("D5/") for file in result.files))

    def test_source_universe_annotation_and_constant_application_share_captured_level(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            original = 'Template.realize signature.{u} (fun λ (I : Type u) (J : Sort u) => ("Type u", I, J))'
            row = fixture.registration(readout=original)
            row["extra_level_params"] = ["u_1"]
            constant = fixture.specialize(row, "readout", "signature.{u}", ["u_1"])
            slot = fixture.syntax["files"][0]["commands"][0]["slots"]["readout"]
            slot["identifiers"][0]["source_levels"] = [{"kind": "param", "name_components": ["u"]}]
            parameter = self.universe_specialization(fixture, row, "Type u", "u_1")
            sort_parameter = self.universe_specialization(fixture, row, "Sort u", "u_1")
            row["source_specializations"]["readout"].reverse()
            row["type_arg_source_slots"] = [None, None, "readout", None, None, None, None, None]
            row["type_args"][2] = None
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [failure.as_dict() for failure in result.failures])
            expected = 'Template.realize signature.{u_1} (fun λ (I : Type (u_1)) (J : Sort (u_1)) => ("Type u", I, J))'
            self.assertEqual(result.registrations[0].readout, expected)
            self.assertIn("readout := some (" + expected + ")", result.files[0].text)
            self.assertIn("(type_of% (" + expected + "))", result.files[0].text)
            self.assertEqual(result.audit["source_specializations"][0]["entries"], [constant, parameter, sort_parameter])

    def test_invalid_or_ambiguous_source_universe_annotations_fail_without_writes(self) -> None:
        for malformed, code in (("ambiguous", "ambiguous_source_universe_mapping"),
                                ("wrong_byte_span", "source_specialization_span_mismatch"),
                                ("not_ast_universe", "source_specialization_span_mismatch"),
                                ("wrong_term", "source_specialization_term_mismatch"),
                                ("multiple_levels", "invalid_source_specialization"),
                                ("undeclared_level", "missing_level_params")):
            with self.subTest(malformed=malformed), tempfile.TemporaryDirectory() as directory:
                fixture = Fixture(Path(directory))
                row = fixture.registration(readout="Template.realize (fun (I : Type u) (J : Sort u) => (I, J))")
                row["extra_level_params"] = ["u_1", "v_1"]
                entry = self.universe_specialization(fixture, row, "Type u", "u_1")
                if malformed == "ambiguous":
                    self.universe_specialization(fixture, row, "Sort u", "v_1")
                elif malformed == "wrong_byte_span":
                    entry["start"] += 1
                    entry["end"] += 1
                elif malformed == "not_ast_universe":
                    fixture.syntax["files"][0]["commands"][0]["slots"]["readout"]["universe_occurrences"] = []
                elif malformed == "wrong_term":
                    entry["term"] = "(v_1)"
                elif malformed == "multiple_levels":
                    entry["levels"] = ["u_1", "v_1"]
                else:
                    entry.update(term="(w)", levels=["w"], level_params=["w"])
                fixture.save()
                self.assert_failure_writes_nothing(fixture, code)

    def test_compiled_universe_arrays_reject_open_markers_and_placeholders_without_writes(self) -> None:
        for category in ("registration", "template"):
            for level, code in (("?u.7", "unclosed_universe"), ("max 1 ?m.9", "unclosed_universe"),
                                (" ?_mvar.2331 + 1", "unclosed_universe"), ("max 1 (?_uniq.42)", "unclosed_universe"),
                                ("_", "unclosed_universe"), ("max (_+1) u_1", "unclosed_universe"),
                                (None, "invalid_universe"), ("", "invalid_universe")):
                with self.subTest(category=category, level=level), tempfile.TemporaryDirectory() as directory:
                    fixture = Fixture(Path(directory))
                    if category == "registration":
                        row = fixture.registration()
                        row["registration_universes"][0] = level
                    else:
                        row = fixture.template()
                        row["enrollment_universes"][0] = level
                    fixture.save()
                    self.assert_failure_writes_nothing(fixture, code)

    def test_missing_captured_normalized_bridge_arena_cannot_fall_back_to_source_object_arena(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            row = fixture.registration()
            row["bridge_arena_from_source"] = False
            row["bridge_arena"] = None
            fixture.save()
            self.assert_failure_writes_nothing(fixture, "missing_material")

    def test_sealed_catalog_escapes_declaration_keyword_and_preserves_name_identity(self) -> None:
        from reg_migration.render import render_seal

        with tempfile.TemporaryDirectory() as directory:
            fixture = Fixture(Path(directory))
            fixture.registration()
            mapping = fixture.root_catalog(sealed=True)
            fixture.save()
            result = fixture.generator().plan()
            self.assertFalse(result.failures, [failure.as_dict() for failure in result.failures])
            root = next(file for file in result.files if file.kind == "root")
            self.assertIn("def «seal» : Contract.Seal", root.text)
            self.assertNotIn("\ndef seal ", root.text)
            direct = render_seal(result.seals[0], mapping["destination_module"])
            self.assertIn("def «seal» : LeanInformationAudit.Contract.Seal", direct)
            seal_row = next(row for row in result.audit["reconciliation"] if row["category"] == "seals")
            self.assertEqual(seal_row["output_decl"], mapping["destination_module"] + ".seal")



if __name__ == "__main__":
    unittest.main()
