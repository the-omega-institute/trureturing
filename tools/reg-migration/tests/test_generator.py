from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
PACKAGE_DIR = ROOT / "tools" / "reg-migration"
spec = importlib.util.spec_from_file_location("reg_migration", PACKAGE_DIR / "__init__.py", submodule_search_locations=[str(PACKAGE_DIR)])
assert spec and spec.loader
package = importlib.util.module_from_spec(spec)
sys.modules["reg_migration"] = package
spec.loader.exec_module(package)

from reg_migration.lean_syntax import parse_repository
from reg_migration.render import options_literal, render_registration
from reg_migration.model import Registration, Span
from reg_migration.generator import Generator


class GeneratorTests(unittest.TestCase):
  def test_synthetic_parser_and_renderer(self) -> None:
    with tempfile.TemporaryDirectory() as directory:
      tmp_path = Path(directory)
      reg = tmp_path / "Reg" / "D5" / "Sample.lean"
      reg.parent.mkdir(parents=True)
      reg.write_text(
          """import LeanInformationAuditInterface.Syntax
  set_option maxRecDepth 100000
  register_information_theorem Sample.claim in arena
    readout via (Template.realize x)
    primitives actual.toPrimitiveBundle realization bridge
    variation varying sensitivity sensitive
    escape from (Nat) escape continues (open)
  """,
          encoding="utf-8",
      )
      registrations, templates, roots, seals, _ = parse_repository(tmp_path)
      self.assertEqual(len(registrations), 1)
      item = registrations[0]
      self.assertEqual(item.theorem, "Sample.claim")
      self.assertEqual(item.readout, "Template.realize x")
      self.assertEqual(item.continuation, "open")
      self.assertEqual(item.options["maxRecDepth"], 100000)
      rendered = render_registration(item)
      self.assertIn("Contract.Registration", rendered)
      self.assertIn("continuation := .unknown", rendered)
      self.assertEqual(templates, [])
      self.assertEqual(roots, [])
      self.assertEqual(seals, [])


  def test_option_literal_is_sorted_and_typed(self) -> None:
    self.assertEqual(options_literal({"z": True, "a": 3}), "#[{ name := `a, value := .nat 3 }, { name := `z, value := .bool true }]")


  def test_inline_bridge_is_kept_in_render(self) -> None:
    item = Registration(Path("Reg/D5/X.lean"), Span(0, 1), "D5.X.claim", "D5.X.arena", inline_bridge=("fun _ => 0", "by rfl"))
    output = render_registration(item)
    self.assertIn("__p2b_inline_bridge_1", output)
    self.assertIn("by rfl", output)


  def test_fix9_contract_shape_has_value_only_refs(self) -> None:
    item = Registration(Path("Reg/D5/X.lean"), Span(0, 1), "D5.X.claim", "arena", primitive="actual.toPrimitiveBundle", realization="bridge")
    output = render_registration(item)
    self.assertNotIn("targetName :=", output)
    self.assertIn("arena := ⟨arena⟩", output)
    self.assertNotIn("arena := ⟨`", output)


  def test_missing_snapshot_is_fail_closed(self) -> None:
    with tempfile.TemporaryDirectory() as directory:
      root = Path(directory)
      source = root / "Reg" / "D5" / "Sample.lean"
      source.parent.mkdir(parents=True)
      source.write_text("register_information_theorem claim in arena\n", encoding="utf-8")
      report = root / "report.json"
      report.write_text(json.dumps({"modules": []}), encoding="utf-8")
      mapping = root / "mapping.json"
      mapping.write_text(json.dumps({"modules": []}), encoding="utf-8")
      result = Generator(root, report, mapping).plan()
      self.assertTrue(any(f.code == "missing_compiled_input" for f in result.failures))
      with self.assertRaises(Exception):
        Generator(root, report, mapping).write(result, root / "out")


  def test_plan_and_render_are_deterministic(self) -> None:
    with tempfile.TemporaryDirectory() as directory:
      root = Path(directory)
      source = root / "Reg" / "D5" / "Sample.lean"
      source.parent.mkdir(parents=True)
      source.write_text("register_information_theorem claim in arena\n", encoding="utf-8")
      key = {"root": "Reg.D5.Sample", "registration_module": "Reg.D5.Sample", "theorem": "D5.Sample.claim", "object_arena": "arena", "catalog": "arena"}
      report = root / "report.json"
      report.write_text(json.dumps({"modules": [{"module": "Reg.D5.Sample", "information_templates": {"records": [{"key": key, "unit_name": "unit", "bridge_kind": "legacy"}]}}]}, sort_keys=True), encoding="utf-8")
      mapping = root / "mapping.json"
      mapping.write_text(json.dumps({"modules": []}), encoding="utf-8")
      first = Generator(root, report, mapping).plan()
      second = Generator(root, report, mapping).plan()
      self.assertFalse(first.failures)
      self.assertEqual([(f.path, f.text) for f in first.files], [(f.path, f.text) for f in second.files])


if __name__ == "__main__":
  unittest.main()
