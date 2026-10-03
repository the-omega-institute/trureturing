from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


PARSER = os.environ.get("REG_MIGRATION_PARSER")
IMPORTS = "import LeanInformationAuditInterface.Syntax\n\n"


@unittest.skipUnless(PARSER, "set REG_MIGRATION_PARSER and inherit the package Lake LEAN_PATH to run compiled Lean parser integration")
class LeanParserIntegrationTests(unittest.TestCase):
    def invoke(self, arguments: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run([str(PARSER), *arguments], cwd=cwd, text=True, encoding="utf-8", capture_output=True, timeout=120)

    def parse(self, root: Path, source: str, path: str = "Reg/D5/Sample.lean") -> dict:
        file = root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(source, encoding="utf-8")
        result = self.invoke(["--one", str(root), path], root.parent)
        self.assertEqual(result.returncode, 0, result.stderr)
        value = json.loads(result.stdout)
        self.assertEqual(value["path"], path)
        self.assertEqual(value["source_text"], source)
        self.assertEqual([name for name in value["imports"] if name != "Init"], ["LeanInformationAuditInterface.Syntax"])
        raw = source.encode("utf-8")
        for command in value["commands"]:
            self.assertLess(command["start"], command["end"])
            raw[command["start"]:command["end"]].decode("utf-8")
            for slot in command["slots"].values():
                self.assertLessEqual(command["start"], slot["start"])
                self.assertLessEqual(slot["end"], command["end"])
                self.assertEqual(raw[slot["start"]:slot["end"]].decode("utf-8"), slot["text"])
                for occurrence in slot["universe_occurrences"]:
                    self.assertLessEqual(slot["start"], occurrence["start"])
                    self.assertLessEqual(occurrence["end"], slot["end"])
                    self.assertEqual(raw[occurrence["start"]:occurrence["end"]].decode("utf-8"), occurrence["text"])
        return value

    def test_actual_registration_grammar_variants_and_keyword_slots(self) -> None:
        source = IMPORTS + """register_information_theorem legacyClaim in arena
  primitives actual.toPrimitiveBundle realization bridge variation varying sensitivity sensitive
register_information_theorem inlineClaim in arena
  primitives actual.toPrimitiveBundle realization inline actual := by exact originalBridge
register_information_theorem forwardClaim via (@descriptor.{u, v}) in arena output_evidence outputProof
register_information_theorem forwardReadout via descriptor in arena
  readout via (Template.realize x) output_evidence outputProof
  escape from (Nat) escape continues (residual)
register_information_theorem occurrenceClaim in arena object_arena objectArena catalog catalog
  readout via (Template.realize x) primitives actual.toPrimitiveBundle realization bridge
  variation varying sensitivity sensitive escape from (Nat) escape continues (open)
register_information_theorem sourceClaim in arena
  readout via (Template.realize x) realizes familyRecord
  escape from source (selectedSource) escape continues (open)
register_information_theorem finiteSourceClaim in arena
  readout via (Template.realize x) realizes familyRecord
  finite via finiteBridge variation varying sensitivity sensitive
  escape from source (selectedSource) escape continues (residual)
information_theorem nativeClaim in arena
  readout via (Template.realize x) primitives actual variation varying sensitivity sensitive
  escape from (Nat) escape continues (open) : ∀ (α : Type u), True := by intro α; exact True.intro
information_theorem nativeOccurrence in arena object_arena objectArena catalog catalog
  primitives actual variation varying sensitivity sensitive : True := by exact True.intro
private theorem privateClaim : True := by exact True.intro
register_information_theorem privateClaim in arena
  primitives actual.toPrimitiveBundle realization bridge
register_information_theorem D5.Sample.«claim with space.λ» in arena
  primitives actual.toPrimitiveBundle realization bridge
"""
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        commands = [item for item in value["commands"] if item["kind"] == "registration"]
        self.assertEqual(len(commands), 11)
        by_name = {item["slots"]["theorem"]["text"]: item for item in commands}
        self.assertEqual(by_name["legacyClaim"]["variant"], "legacy")
        self.assertEqual(by_name["forwardClaim"]["variant"], "forward")
        self.assertEqual(by_name["occurrenceClaim"]["variant"], "occurrence")
        self.assertEqual(by_name["sourceClaim"]["variant"], "source")
        self.assertEqual(by_name["finiteSourceClaim"]["variant"], "finite-source")
        self.assertEqual(by_name["nativeClaim"]["variant"], "native")
        self.assertEqual(by_name["inlineClaim"]["slots"]["inline_proof"]["text"], "by exact originalBridge")
        self.assertEqual(by_name["inlineClaim"]["slots"]["inline_actual"]["text"], "actual")
        self.assertEqual(by_name["forwardClaim"]["slots"]["via_descriptor"]["text"], "(@descriptor.{u, v})")
        descriptor = by_name["forwardClaim"]["slots"]["via_descriptor"]
        explicit = [identifier for identifier in descriptor["identifiers"] if identifier["explicit_universes"]]
        self.assertEqual(len(explicit), 1)
        self.assertEqual(explicit[0]["head_text"], "descriptor")
        self.assertEqual(explicit[0]["source_levels"], [
            {"kind": "param", "name_components": ["u"]},
            {"kind": "param", "name_components": ["v"]},
        ])
        self.assertEqual([(item["text"], item["name_components"]) for item in descriptor["universe_occurrences"]], [
            ("u", ["u"]), ("v", ["v"]),
        ])
        self.assertEqual(by_name["forwardClaim"]["slots"]["output_evidence"]["text"], "outputProof")
        self.assertEqual(by_name["sourceClaim"]["slots"]["escape_from_source"]["text"], "selectedSource")
        self.assertEqual(by_name["finiteSourceClaim"]["slots"]["finite_bridge"]["text"], "finiteBridge")
        target_type = by_name["nativeClaim"]["slots"]["target_type"]
        self.assertEqual(target_type["text"], "∀ (α : Type u), True")
        self.assertEqual([(item["text"], item["name_components"]) for item in target_type["universe_occurrences"]], [("u", ["u"])])
        self.assertEqual(by_name["nativeClaim"]["slots"]["native_proof"]["text"], "by intro α; exact True.intro")
        self.assertIn("privateClaim", by_name)
        self.assertIn("D5.Sample.«claim with space.λ»", by_name)

    def test_actual_nested_terms_comments_strings_and_utf8_offsets(self) -> None:
        readout = 'Template.realize (fun (α : Type u) (β : Sort v) x => (let marker := "primitives escape continues λ Type u Sort v descriptor.{u}"; (x, (marker, "後"))))'
        prefix = IMPORTS + '-- α register_information_theorem falseClaim in arena\n/- 外 /- primitives realization -/ readout via -/\ndef keywordString := "variation sensitivity escape from"\n'
        source = prefix + "register_information_theorem «真命题» in arena\n  readout via (" + readout + ")\n  primitives (actual.toPrimitiveBundle) realization bridge\n  escape from (Nat × (String × Nat)) escape continues (by exact residual)\n"
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        commands = [item for item in value["commands"] if item["kind"] == "registration"]
        self.assertEqual(len(commands), 1)
        item = commands[0]
        self.assertEqual(item["start"], len(prefix.encode("utf-8")))
        self.assertNotEqual(item["start"], len(prefix))
        self.assertEqual(item["slots"]["readout"]["text"], readout)
        self.assertEqual(item["slots"]["escape_from"]["text"], "Nat × (String × Nat)")
        self.assertEqual(item["slots"]["continuation"]["text"], "by exact residual")
        raw = source.encode("utf-8")
        identifiers = item["slots"]["readout"]["identifiers"]
        self.assertTrue(any(identifier["head_text"] == "Template.realize" for identifier in identifiers))
        for identifier in identifiers:
            self.assertEqual(raw[identifier["start"]:identifier["end"]].decode("utf-8"), identifier["text"])
        occurrences = item["slots"]["readout"]["universe_occurrences"]
        self.assertEqual([(entry["text"], entry["name_components"]) for entry in occurrences], [("u", ["u"]), ("v", ["v"])])
        self.assertTrue(all(entry["start"] < raw.index(b'let marker') for entry in occurrences))

    def test_actual_templates_three_root_entries_seal_and_notation(self) -> None:
        source = IMPORTS + """register_information_template SimpleTemplate
register_information_template ConstructorTemplate constructors 7 [ConstructorTemplate.second, ConstructorTemplate.first]
run_cmd RootCatalogs.declare {
  rootId := `Reg.D5.Sample, expected := #[], source := #[], baseline := #[], companionPrefix := none }
run_cmd do
  let statement ← captureStatement `D5.Sample.claim
  RootCatalogs.declare {
    rootId := `Reg.D5.Sample
    expected := #[{ theoremName := `D5.Sample.z }, { theoremName := `D5.Sample.a }]
    source := #[]
    baseline := #[]
    companionPrefix := none }
run_cmd RootCatalogs.declare Support.contract
#seal_information_theory
local notation "view" => Template.realize x
"""
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        templates = [item for item in value["commands"] if item["kind"] == "template"]
        roots = [item for item in value["commands"] if item["kind"] == "root"]
        self.assertEqual(len(templates), 2)
        self.assertEqual(templates[1]["slots"]["version"]["text"], "7")
        self.assertEqual(templates[1]["constructors"], ["ConstructorTemplate.second", "ConstructorTemplate.first"])
        self.assertEqual(templates[1]["slots"]["constructor_0"]["text"], "ConstructorTemplate.second")
        self.assertEqual(templates[1]["slots"]["constructor_1"]["text"], "ConstructorTemplate.first")
        self.assertEqual(len(roots), 3)
        self.assertEqual([item["variant"] for item in roots], ["root-literal", "root-literal", "root-reference"])
        self.assertEqual(roots[2]["slots"]["root_contract"]["text"], "Support.contract")
        expected = roots[1]["slots"]["expected"]["text"]
        self.assertLess(expected.index("D5.Sample.z"), expected.index("D5.Sample.a"))
        self.assertEqual(len([item for item in value["commands"] if item["kind"] == "seal"]), 1)
        self.assertEqual(len([item for item in value["commands"] if item["kind"] == "notation"]), 1)

    def test_actual_namespace_section_scoped_options_and_private_declarations(self) -> None:
        source = IMPORTS + """namespace Outer
namespace MatrixObservation
def matrixIdentity := True
end MatrixObservation
open MatrixObservation
universe u v
section Scoped
set_option maxRecDepth 91
open Classical in
set_option pp.universes true in
  register_information_theorem scopedClaim in arena primitives actual.toPrimitiveBundle realization bridge
private theorem «private claim» : True := by exact unresolvedProof
end Scoped
register_information_theorem outsideClaim in arena primitives actual.toPrimitiveBundle realization bridge
end Outer
register_information_theorem rootClaim in arena primitives actual.toPrimitiveBundle realization bridge
"""
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        registrations = [item for item in value["commands"] if item["kind"] == "registration"]
        self.assertEqual([item["slots"]["theorem"]["text"] for item in registrations], ["scopedClaim", "outsideClaim", "rootClaim"])
        self.assertEqual([item["namespace"] for item in registrations], ["Outer", "Outer", ""])
        self.assertEqual([item["ambient_universes"] for item in registrations], [["u", "v"], ["u", "v"], []])
        for registration in registrations[:2]:
            self.assertTrue(any(item.get("namespace") == "Outer.MatrixObservation" and
                                item.get("namespace_components") == ["Outer", "MatrixObservation"]
                                for item in registration["open_decls"]))
        self.assertEqual(registrations[2]["open_decls"], [])
        self.assertTrue(any("set_option maxRecDepth 91" in source[item["start"]:item["end"]] for item in value["commands"]))
        wrappers = registrations[0]["scope_wrappers"]
        self.assertEqual(len(wrappers), 2)
        raw = source.encode("utf-8")
        for wrapper in wrappers:
            self.assertEqual(raw[wrapper["start"]:wrapper["end"]].decode("utf-8"), wrapper["text"])
            self.assertLessEqual(wrapper["end"], registrations[0]["start"])
        prefix = raw[min(wrapper["start"] for wrapper in wrappers):registrations[0]["start"]].decode("utf-8")
        self.assertIn("open Classical in", prefix)
        self.assertIn("set_option pp.universes true in", prefix)
        self.assertTrue(any("private claim" in source.encode("utf-8")[item["start"]:item["end"]].decode("utf-8") for item in value["commands"]))

    def test_actual_parser_does_not_elaborate_or_execute_source_commands(self) -> None:
        source = IMPORTS + """def impossibleType : UnknownType := UnknownValue
theorem impossibleProof : False := by exact unknownProof
run_cmd panic! "SOURCE COMMAND EXECUTED"
register_information_theorem unknownTheorem in unknownArena
  primitives unknownPrimitives realization unknownBridge
"""
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        self.assertEqual(len(value["commands"]), 4)
        self.assertEqual(value["commands"][-1]["kind"], "registration")

    def test_actual_companion_identifier_spans_exclude_name_literals(self) -> None:
        source = IMPORTS + """def value := D5.Sample.claim.__information_unit.Statement
def quoted := `D5.Sample.claim.__information_unit
def realizationValue := D5.Sample.claim.__primitive_realization
"""
        with tempfile.TemporaryDirectory() as directory:
            value = self.parse(Path(directory), source)
        consumers = [identifier for item in value["commands"] for identifier in item["companion_identifiers"]]
        self.assertEqual(len(consumers), 2)
        self.assertEqual(consumers[0]["name"], "D5.Sample.claim.__information_unit")
        self.assertEqual(consumers[0]["text"], "D5.Sample.claim.__information_unit.Statement")
        self.assertEqual(consumers[1]["name"], "D5.Sample.claim.__primitive_realization")
        for identifier in consumers:
            self.assertEqual(source.encode("utf-8")[identifier["start"]:identifier["end"]].decode("utf-8"), identifier["text"])

    def test_actual_manifest_handles_spaced_paths_different_cwd_and_source_order(self) -> None:
        with tempfile.TemporaryDirectory(prefix="parser integration ") as directory:
            parent = Path(directory)
            root = parent / "repo with spaces"
            files = []
            for name in ("Z", "A"):
                path = "Reg/D5/" + name + ".lean"
                file = root / path
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(IMPORTS + "register_information_template " + name + "\n", encoding="utf-8")
                files.append({"path": path})
            manifest = parent / "source manifest.json"
            output = parent / "parser output.json"
            manifest.write_text(json.dumps({"repo": str(root), "files": files}), encoding="utf-8")
            result = self.invoke(["--manifest", str(manifest), str(output)], parent)
            self.assertEqual(result.returncode, 0, result.stderr)
            snapshot = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(snapshot["schema"], "reg-migration-syntax-v1")
            self.assertEqual([item["path"] for item in snapshot["files"]], sorted(item["path"] for item in files))
            before = output.read_bytes()
            manifest.write_text(json.dumps({"repo": str(root), "files": list(reversed(files))}), encoding="utf-8")
            result = self.invoke(["--manifest", str(manifest), str(output)], parent)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), before)

    def test_actual_unknown_syntax_fails_before_publishing_any_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            good = root / "Reg/D5/Good.lean"
            bad = root / "Reg/D5/Unknown.lean"
            good.parent.mkdir(parents=True)
            good.write_text(IMPORTS + "register_information_template Template\n", encoding="utf-8")
            bad.write_text(IMPORTS + "register_information_new newGrammar\n", encoding="utf-8")
            result = self.invoke(["--one", str(root), "Reg/D5/Unknown.lean"], root)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("RM-SYNTAX-PARSE", result.stderr)
            manifest = root / "manifest.json"
            output = root / "output.json"
            manifest.write_text(json.dumps({"repo": str(root), "files": [{"path": "Reg/D5/Good.lean"}, {"path": "Reg/D5/Unknown.lean"}]}), encoding="utf-8")
            result = self.invoke(["--manifest", str(manifest), str(output)], root)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())
            output.write_text("retained output", encoding="utf-8")
            result = self.invoke(["--manifest", str(manifest), str(output)], root)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(encoding="utf-8"), "retained output")


if __name__ == "__main__":
    unittest.main()
