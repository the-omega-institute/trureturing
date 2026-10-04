"""Executable contracts for occurrence verdict comparison (Python 3.12+)."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PROGRAM = Path(__file__).resolve().parents[1] / "reg-verdict-compare.py"
H = "a" * 64
J = "b" * 64
ROOT = "Reg.Example"


def key(arena="Arena.first"):
    return dict(root=ROOT, registration_module=ROOT, theorem="D5.Example.result",
                object_arena=arena, catalog=arena)


def record(arena="Arena.first", state="declared_validated"):
    k = key(arena)
    certificate = dict(key=copy.deepcopy(k), evidence_ref=H, plan_identity=H,
                       descriptor_identity=H, actual_identity=H,
                       argument_inputs=[], extraction_inputs=[])
    return dict(key=k, registration_source_path="Reg/Example.lean",
                binding_source_path="Reg/Example.lean", statement_identity=H,
                state=state, diagnostic=None if state == "declared_validated" else "IE-C050 input",
                certificate=certificate if state == "declared_validated" else None,
                unit_name="D5.Example.result.__information_unit",
                realization_name="Reg.Example.realization", bridge_kind="legacy",
                escape_from=dict(name="Arena.first", type_identity=H, object_identity=H),
                escape_continues=dict(kind="open", declaration_name=None,
                                      statement_identity=None, chain_name=None))


def declaration(name="Arena.first.__catalog_irredundant"):
    return dict(name=name, name_key="n0", kind="theorem", include_in_statement=True,
                axioms=[], type_sha256="sha256:" + H, statement_id="sha256:" + H)


def report(records=None):
    records = [record()] if records is None else records
    return dict(schema="stratalint-raw-lean-report-v2", modules=[dict(
        module=ROOT, source_path="Reg/Example.lean", source_sha256="sha256:" + H,
        imports=[], declarations=[declaration()], information_registration_errors=[],
        information_templates=dict(schema_version=1, compatibility_version=17,
                                   inventory=[copy.deepcopy(x["key"]) for x in records],
                                   registered=[copy.deepcopy(x["key"]) for x in records],
                                   records=records))])


def seal():
    row = dict(theorem="D5.Example.result", unit="D5.Example.result.__information_unit",
               index=0, primitive_count=2, primitive_axes=["left", "right"],
               primitive_kernel_address=H, unique_capture_count=2, full_escape_count=0,
               without_escape_count=2, unique_capture_by_role_signature={"left": 2},
               gain_rate=dict(numerator=2, denominator=2), lowers_escape=True,
               certificate="D5.Example.result.__lowers_escape", proof_method="direct")
    return dict(schema="lean-intrinsic-information-escape-seal",
                catalog_mode="single-compilation-leave-one-out", arenas=[dict(
                    arena="Arena.first", catalog="Arena.first.__information_catalog",
                    verdict="irredundant", verdict_certificate="Arena.first.__catalog_irredundant",
                    state_card=2, off_diagonal_pair_count=2, full_escape_count=0,
                    full_escape_rate=dict(numerator=0, denominator=2), theorems=[row])])


def sealed_report():
    r = report()
    r["modules"][0]["declarations"] += [declaration("D5.Example.result.__lowers_escape"),
                                          declaration("Arena.first.__information_catalog"),
                                          declaration("D5.Example.result.__information_unit")]
    return r


def relocation(field, before, after):
    return dict(schema="reg-verdict-relocations-v1", field=field, before=before, after=after)


def source_record():
    row = record()
    row["bridge_kind"] = "source-equivalence"
    row["escape_from"]["name"] = row["key"]["theorem"]
    row["certificate"]["source_binding"] = dict(
        source_owner="D5.Example", source_name=row["key"]["theorem"], source_type_identity=H,
        telescope_size=2, level_count=0, coordinates=[], coordinate_paths=[],
        registration_identity=H, readouts=[dict(
            occurrence_identity=H, path=["body", side], scope_paths=[["body"]],
            scope_size=1, state_binder=0) for side in ("fn", "arg")])
    row["certificate"]["extraction_inputs"] = [dict(
        name=name, owner=owner, type_identity=H, body_identity=H) for name, owner in
        ((row["key"]["theorem"], "D5.Example"), (row["realization_name"], ROOT),
         (row["key"]["object_arena"], ROOT))]
    return row


class CompareTests(unittest.TestCase):
    def run_compare(self, before, after, mapping=None, seals=None, raw=None):
        with tempfile.TemporaryDirectory(prefix="verdict compare ") as directory:
            root = Path(directory)
            left, right = root / "before report.json", root / "after report.json"
            left.write_text(json.dumps(before), encoding="utf-8")
            right.write_text(raw if raw is not None else json.dumps(after), encoding="utf-8")
            command = [sys.executable, str(PROGRAM), str(left), str(right)]
            input_text = None
            if mapping is not None:
                command += ["--mapping", "-"]
                input_text = "\n".join(json.dumps(x) for x in mapping)
            if seals is not None:
                for option, artifact in zip(("--before-seal", "--after-seal"), seals):
                    path = root / (option + ".json")
                    path.write_text(json.dumps(artifact), encoding="utf-8")
                    command += [option, ROOT, str(path)]
            paths = set(root.iterdir())
            result = subprocess.run(command, input=input_text, text=True, capture_output=True,
                                    cwd=root, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            self.assertEqual(set(root.iterdir()), paths, "comparison writes only stdout")
            self.assertEqual(result.stderr, "")
            return result.returncode, json.loads(result.stdout)

    def test_multiple_arenas_preserve_occurrences(self):
        r = report([record(), record("Arena.second")])
        code, result = self.run_compare(r, r)
        self.assertEqual(code, 0)
        self.assertEqual(result["matched_records"], 2)

    def test_same_theorem_arena_with_distinct_catalogs(self):
        other = record()
        other["key"]["catalog"] = other["certificate"]["key"]["catalog"] = "Catalog.other"
        r = report([record(), other])
        code, result = self.run_compare(r, r)
        self.assertEqual(code, 0)
        self.assertEqual(result["matched_records"], 2)

    def test_same_totals_with_swapped_states(self):
        before = report([record(), record("Arena.second", "declared_unresolved")])
        after = report([record(state="declared_unresolved"), record("Arena.second")])
        code, result = self.run_compare(before, after)
        self.assertEqual(code, 1)
        self.assertTrue(any(x["path"] == "/state" for x in result["differences"]))

    def test_each_side_validates_independently(self):
        for side in (0, 1):
            for field in ("inventory", "registered", "records"):
                pair = [report(), report()]
                pair[side]["modules"][0]["information_templates"][field] = []
                with self.subTest(side=side, field=field):
                    self.assertEqual(self.run_compare(*pair)[0], 2)

    def test_missing_extra_and_duplicate_occurrences(self):
        base = report([record(), record("Arena.second")])
        for changed in (report(), report([record(), record("Arena.second"), record("Arena.third")]),
                        report([record(), record()])):
            with self.subTest(changed=changed):
                self.assertEqual(self.run_compare(base, changed)[0], 2)

    def test_unknown_schemas_and_fields(self):
        for changed in (dict(report(), schema="unknown"), report()):
            if changed["schema"] != "unknown":
                changed["modules"][0]["information_templates"]["schema_version"] = 2
            self.assertEqual(self.run_compare(report(), changed)[0], 2)
        changed = report()
        changed["modules"][0]["information_templates"]["records"][0]["extra"] = 1
        self.assertEqual(self.run_compare(report(), changed)[0], 2)

    def test_null_inventory_is_not_empty(self):
        for field in ("information_templates", "inventory", "registered", "records"):
            changed = report([])
            if field == "information_templates":
                changed["modules"][0][field] = None
            else:
                changed["modules"][0]["information_templates"][field] = None
            self.assertEqual(self.run_compare(report([]), changed)[0], 2)
        self.assertEqual(self.run_compare(report([]), report([]))[0], 0)

    def test_duplicate_json_members_and_nonfinite_numbers(self):
        self.assertEqual(self.run_compare(report(), report(), raw='{"schema":"a","schema":"b","modules":[]}')[0], 2)
        raw = json.dumps(report()).replace('"compatibility_version": 18', '"compatibility_version": NaN')
        self.assertEqual(self.run_compare(report(), report(), raw=raw)[0], 2)

    def test_duplicate_modules_and_declarations(self):
        for field in ("modules", "declarations"):
            changed = report()
            target = changed[field] if field == "modules" else changed["modules"][0][field]
            target.append(copy.deepcopy(target[0]))
            self.assertEqual(self.run_compare(report(), changed)[0], 2)

    def test_malformed_nested_field_types_are_input_errors(self):
        for field, value in (("state", []), ("bridge_kind", {}), ("certificate", []),
                             ("escape_from", "source"), ("key", None)):
            changed = report()
            changed["modules"][0]["information_templates"]["records"][0][field] = value
            self.assertEqual(self.run_compare(report(), changed)[0], 2)

    def test_noninjective_and_unused_mapping(self):
        r = report([record(), record("Arena.second")])
        for mapping in ([relocation("object_arena", "Arena.first", "Arena.second")],
                        [relocation("root", ROOT, "Reg.New"), relocation("root", "Reg.Other", "Reg.New")],
                        [relocation("root", "Reg.Other", "Reg.New")]):
            self.assertEqual(self.run_compare(r, r, mapping)[0], 2)

    def test_forbidden_mapping_fields_and_unknown_mapping_schema(self):
        for mapping in (relocation("theorem", "D5.Example.result", "D5.Other.result"),
                        relocation("statement_identity", H, J),
                        dict(relocation("root", ROOT, "Reg.New"), schema="unknown")):
            self.assertEqual(self.run_compare(report(), report(), [mapping])[0], 2)

    def test_duplicate_mapping_source_is_an_error(self):
        mapping = relocation("root", ROOT, ROOT)
        self.assertEqual(self.run_compare(report(), report(), [mapping, mapping])[0], 2)

    def test_compatibility_versions_are_independent(self):
        changed = report()
        changed["modules"][0]["information_templates"]["compatibility_version"] = 18
        self.assertEqual(self.run_compare(report(), changed)[0], 0)

    def test_arena_and_catalog_relocations_are_exact(self):
        before, after = report(), report([record("Arena.second")])
        mapping = [relocation(f, "Arena.first", "Arena.second") for f in ("object_arena", "catalog")]
        self.assertEqual(self.run_compare(before, after, mapping)[0], 0)
        self.assertEqual(self.run_compare(before, after, mapping[:1])[0], 2)

    def test_legal_relocation_and_certificate_identity_changes(self):
        before, after = report(), report()
        module = after["modules"][0]
        module["module"], module["source_path"] = "Reg.Moved", "Reg/Moved.lean"
        evidence = module["information_templates"]
        for k in evidence["inventory"] + evidence["registered"] + [evidence["records"][0]["key"], evidence["records"][0]["certificate"]["key"]]:
            k["root"] = k["registration_module"] = "Reg.Moved"
        row = evidence["records"][0]
        row["binding_source_path"] = row["registration_source_path"] = "Reg/Moved.lean"
        for field in ("evidence_ref", "plan_identity", "descriptor_identity", "actual_identity"):
            row["certificate"][field] = J
        row["escape_from"]["object_identity"] = J
        mapping = [relocation(f, ROOT, "Reg.Moved") for f in ("root", "registration_module", "module")]
        mapping += [relocation("source_path", "Reg/Example.lean", "Reg/Moved.lean")]
        code, result = self.run_compare(before, after, mapping)
        self.assertEqual(code, 0)
        self.assertTrue(any(x["path"] == "/certificate/evidence_ref" for x in result["differences"]))

    def test_target_and_statement_are_invariants(self):
        changed = report()
        changed["modules"][0]["information_templates"]["records"][0]["statement_identity"] = J
        self.assertEqual(self.run_compare(report(), changed)[0], 1)
        changed = report([record("Arena.other")])
        self.assertEqual(self.run_compare(report(), changed)[0], 2)

    def test_bridge_and_escape_slot_changes(self):
        for field, value in (("bridge_kind", "forward"), ("escape_from", None),
                             ("escape_continues", None)):
            changed = report()
            changed["modules"][0]["information_templates"]["records"][0][field] = value
            self.assertEqual(self.run_compare(report(), changed)[0], 1)

    def test_invalid_escape_and_certificate_shapes(self):
        for field in ("certificate", "escape_from", "escape_continues"):
            changed = report()
            changed["modules"][0]["information_templates"]["records"][0][field] = {}
            self.assertEqual(self.run_compare(report(), changed)[0], 2)
        changed = report()
        changed["modules"][0]["information_templates"]["records"][0]["certificate"]["key"]["theorem"] = "D5.Other.result"
        self.assertEqual(self.run_compare(report(), changed)[0], 2)

    def test_report_order_is_not_an_occurrence_identity(self):
        before = report([record(), record("Arena.second")])
        after = copy.deepcopy(before)
        for field in ("inventory", "registered", "records"):
            after["modules"][0]["information_templates"][field].reverse()
        self.assertEqual(self.run_compare(before, after)[0], 0)

    def test_source_readout_order_is_semantic(self):
        before = report([source_record()])
        after = copy.deepcopy(before)
        after["modules"][0]["information_templates"]["records"][0]["certificate"]["source_binding"]["readouts"].reverse()
        self.assertEqual(self.run_compare(before, after)[0], 1)

    def test_function_operand_with_empty_scope(self):
        row = source_record()
        row["certificate"]["source_binding"]["readouts"] = [dict(
            path=["arg"], state_binder=0, scope_size=0, scope_paths=[],
            occurrence_identity=H, function_operand=True)]
        r = report([row])
        self.assertEqual(self.run_compare(r, r)[0], 0)

    def test_source_identities_and_dependency_inputs_are_not_equality_gates(self):
        before = report([source_record()])
        after = copy.deepcopy(before)
        certificate = after["modules"][0]["information_templates"]["records"][0]["certificate"]
        certificate["source_binding"]["registration_identity"] = J
        certificate["source_binding"]["readouts"][0]["occurrence_identity"] = J
        certificate["extraction_inputs"][0]["body_identity"] = J
        self.assertEqual(self.run_compare(before, after)[0], 0)

    def test_missing_seal_does_not_claim_overall_pass(self):
        code, result = self.run_compare(report(), report())
        self.assertEqual(code, 0)
        self.assertEqual(result["seal"], "not_checked")
        self.assertEqual(result["overall"], "not_checked")

    def test_seal_generated_declarations_are_required(self):
        changed = report()
        changed["modules"][0]["declarations"] = []
        self.assertEqual(self.run_compare(report(), changed)[0], 1)

    def test_seal_verdict_and_semantic_array_order(self):
        r = sealed_report()
        self.assertEqual(self.run_compare(r, r, seals=(seal(), seal()))[0], 0)
        for field, value in (("verdict", "redundant"), ("state_card", 3)):
            changed = seal()
            changed["arenas"][0][field] = value
            self.assertEqual(self.run_compare(r, r, seals=(seal(), changed))[0], 1)
        changed = seal()
        changed["arenas"][0]["theorems"][0]["primitive_axes"].reverse()
        self.assertEqual(self.run_compare(r, r, seals=(seal(), changed))[0], 1)

    def test_seal_missing_certificate_declaration_is_input_error(self):
        self.assertEqual(self.run_compare(report(), report(), seals=(seal(), seal()))[0], 2)

    def test_empty_seal_artifact_cannot_cover_a_root(self):
        empty = dict(seal(), arenas=[])
        r = sealed_report()
        self.assertEqual(self.run_compare(r, r, seals=(empty, empty))[0], 2)

    def test_seal_artifact_cannot_omit_a_member(self):
        changed = seal()
        changed["arenas"][0]["theorems"] = []
        r = sealed_report()
        self.assertEqual(self.run_compare(r, r, seals=(changed, changed))[0], 2)

    def test_seal_generated_owner_and_kind_are_preserved(self):
        changed = report()
        changed["modules"][0]["declarations"][0]["kind"] = "def"
        self.assertEqual(self.run_compare(report(), changed)[0], 1)

    def test_seal_member_order_is_semantic(self):
        r = sealed_report()
        r["modules"][0]["declarations"] += [declaration("D5.Other.result.__information_unit"),
                                              declaration("D5.Other.result.__lowers_escape")]
        before = seal()
        other = copy.deepcopy(before["arenas"][0]["theorems"][0])
        other.update(theorem="D5.Other.result", unit="D5.Other.result.__information_unit",
                     certificate="D5.Other.result.__lowers_escape", index=1)
        before["arenas"][0]["theorems"].append(other)
        after = copy.deepcopy(before)
        after["arenas"][0]["theorems"].reverse()
        for i, row in enumerate(after["arenas"][0]["theorems"]):
            row["index"] = i
        self.assertEqual(self.run_compare(r, r, seals=(before, after))[0], 1)

    def test_seal_declaration_relocation(self):
        before, after = report(), report()
        after["modules"][0]["declarations"][0]["name"] = "Arena.second.__catalog_irredundant"
        mapping = [relocation("declaration_name", "Arena.first.__catalog_irredundant",
                              "Arena.second.__catalog_irredundant")]
        self.assertEqual(self.run_compare(before, after, mapping)[0], 0)

    def test_stdout_is_deterministic_across_working_directories(self):
        r = report([record(), record("Arena.second")])
        self.assertEqual(self.run_compare(r, r), self.run_compare(r, r))

    def test_registration_errors_have_separate_differences(self):
        changed = report()
        changed["modules"][0]["information_registration_errors"] = ["IE-C050 changed"]
        code, result = self.run_compare(report(), changed)
        self.assertEqual(code, 1)
        self.assertEqual(result["information_registration_errors"][0]["after"], ["IE-C050 changed"])


if __name__ == "__main__":
    unittest.main()
