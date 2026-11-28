"""Selection and dispatch tests with a mocked portable adapter."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, call, patch

spec = importlib.util.spec_from_file_location("consumer", Path(__file__).with_name("omega-consumer.py"))
consumer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(consumer)

from ci_contract import load, selection
import ci_required


class ConsumerTests(unittest.TestCase):
    graph = {"OmegaInit.Core": set(), "OmegaMath.Base": {"OmegaInit.Core"},
             "OmegaChecks.Portable.Common": {"OmegaInit.Core"},
             "D5.Plain": set(), "D5.Direct": {"OmegaMath.Base", "D5.Plain"},
             "D5.Independent": {"OmegaMath.Base"}, "D5.Inherited": {"D5.Direct"},
             "Reg.Observation": {"D5.Inherited"}, "Reg.Separate": {"D5.Independent"},
             "Trureturing": {"D5.Inherited", "D5.Independent"}}
    eligible = [name for name in graph if name not in {"OmegaInit.Core", "D5.Plain"}]

    def test_downstream_dependencies_and_reg_are_selected(self):
        for path in ("D5/Plain.lean", "D5/Direct.lean"):
            with self.subTest(path=path):
                self.assertEqual(consumer.select(self.graph, self.eligible, [path]),
                                 ["D5.Direct", "D5.Inherited", "Reg.Observation", "Trureturing"])

    def test_only_affected_reg_modules_on_reg_pin_change(self):
        self.assertEqual(consumer.select(self.graph, self.eligible, ["Reg/lake-manifest.json"]),
                         ["Reg.Observation", "Reg.Separate"])

    def test_package_pin_and_adapter_changes_select_all_consumer_roots(self):
        expected = ["D5.Direct", "D5.Independent", "D5.Inherited", "Reg.Observation", "Reg.Separate", "Trureturing"]
        for paths in (None, ["lake-manifest.json"], ["src/OmegaChecks/portable.py"]):
            self.assertEqual(consumer.select(self.graph, self.eligible, paths), expected)

    def test_removed_leaf_is_empty_and_remaining_import_is_an_error(self):
        self.assertEqual(consumer.select(self.graph, self.eligible, ["D5/Removed.lean"]), [])
        graph = dict(self.graph, **{"D5.Direct": {"D5.Removed"}})
        with self.assertRaisesRegex(ValueError, "still imported"):
            consumer.select(graph, self.eligible, ["D5/Removed.lean"])

    def test_discovery_requires_manifest_and_preserves_adapter_selection(self):
        adapter = Mock()
        adapter.import_graph.return_value = ({}, self.graph)
        adapter.consumers.return_value = self.eligible
        with tempfile.TemporaryDirectory() as temporary, patch.object(consumer, "portable_adapter", return_value=(adapter, "lean")):
            manifest = Path(temporary) / "changed"
            with self.assertRaisesRegex(ValueError, "missing changed-path manifest"):
                consumer.discover(manifest)
            manifest.write_bytes(b"D5/Direct.lean\0")
            scope, selected_adapter, lean, discovered = consumer.discover(manifest)
            names = scope["consumers"]
            self.assertFalse(scope["verify_release"])
            self.assertEqual(lean, "lean")
            self.assertIs(selected_adapter, adapter)
            self.assertEqual(names, ["D5.Direct", "D5.Inherited", "Reg.Observation", "Trureturing"])
            adapter.import_graph.assert_called_once_with("lean", with_reg=True)
            adapter.consumers.assert_called_once_with(self.graph)
            consumer.check(names, adapter, discovered)
            adapter.check.assert_called_once_with(names, "both", basis_roots=[], common_roots=(), discovered=discovered)

    def test_hosted_plan_and_dispatch_share_selected_targets(self):
        adapter = Mock()
        adapter.import_graph.return_value = ({}, self.graph)
        adapter.consumers.return_value = self.eligible
        with tempfile.TemporaryDirectory() as temporary, patch.object(consumer, "portable_adapter", return_value=(adapter, "lean")):
            root = Path(temporary)
            changed, scope, targets, output = (root / name for name in ("changed", "scope", "targets", "output"))
            changed.write_bytes(b"Reg/Observation.lean\0")
            with patch.dict(os.environ, {"CI_CHANGED_PATHS_FILE": str(changed), "GITHUB_OUTPUT": str(output)}, clear=True):
                with patch.object(sys, "argv", ["omega-consumer.py", "--write-scope", str(scope), "--cache-targets", str(targets)]):
                    consumer.main()
                self.assertEqual(json.loads(scope.read_text()), {"consumers": ["Reg.Observation"], "verify_release": False})
                self.assertEqual(targets.read_text(), "Reg.Observation\n")
                self.assertEqual(output.read_text().splitlines(), [f"targets-file={targets}", f"report-file={consumer.REPORT}"])
                with patch.dict(os.environ, {"OMEGA_SCOPE_FILE": str(scope)}), patch.object(sys, "argv", ["omega-consumer.py"]):
                    consumer.main()
                adapter.check.assert_called_once_with(["Reg.Observation"], "both", basis_roots=[], common_roots=(), discovered=None)

    def test_release_gate_is_selected_by_pins_receipt_and_verifier(self):
        adapter = Mock()
        adapter.import_graph.return_value = ({}, self.graph)
        adapter.consumers.return_value = self.eligible
        with tempfile.TemporaryDirectory() as temporary, patch.object(consumer, "portable_adapter", return_value=(adapter, "lean")):
            path = Path(temporary) / "changed"
            for changed in sorted(consumer.RELEASE_INPUTS):
                with self.subTest(changed=changed):
                    path.write_bytes(changed.encode() + b"\0")
                    scope, _, _, _ = consumer.discover(path)
                    self.assertTrue(scope["verify_release"])
            scope, _, _, _ = consumer.discover(None)
            self.assertTrue(scope["verify_release"])
            path.write_bytes(b"")
            scope, _, _, _ = consumer.discover(path)
            self.assertFalse(scope["verify_release"])

    def test_required_unit_accounts_for_release_gate_on_both_events(self):
        contract, _ = load(consumer.ROOT)
        for changed in sorted(consumer.RELEASE_INPUTS):
            for purpose in ("pull-request", "push"):
                with self.subTest(path=changed, purpose=purpose):
                    hits = selection(contract, [changed], purpose)["hits"]
                    self.assertTrue(hits["omega-consumer"])
                    self.assertNotIn("omega", hits)
                    needs = {"detect": {"result": "success"},
                             "source": {"result": "success", "outputs": {"source_status": "accepted", "continuation": "true"}}}
                    needs.update({name: {"result": "success" if hit else "skipped", "outputs": {"unit": name} if hit else {}}
                                  for name, hit in hits.items()})
                    with patch.dict(os.environ, {"NEEDS": json.dumps(needs), "HITS": json.dumps(hits)}), patch("builtins.print"):
                        self.assertEqual(ci_required.main(), 0)
                    needs["omega-consumer"]["result"] = "skipped"
                    with patch.dict(os.environ, {"NEEDS": json.dumps(needs), "HITS": json.dumps(hits)}), patch("builtins.print"):
                        self.assertEqual(ci_required.main(), 1)

    def test_release_gate_prepares_only_external_imports_of_public_targets(self):
        adapter = Mock()
        upstream = adapter.upstream_portable.return_value
        graph = {"OmegaMath": {"OmegaMath.Core", "OmegaMathlib.Facade"},
                 "OmegaMath.Core": {"Mathlib.Algebra.Group.Basic"},
                 "OmegaMath.Extra": {"Mathlib.Algebra.Ring.Basic"},
                 "OmegaMathlib": {"Mathlib.Data.List.Basic"},
                 "OmegaMathlib.Facade": {"Mathlib.Data.Nat.Basic", "Init.Prelude", "Batteries.Data.List.Basic"},
                 "OmegaInit": {"OmegaInit.Core"},
                 "OmegaInit.Core": {"Mathlib.Init"},
                 "OmegaBuild.Commands": {"Mathlib.Tactic.Basic"},
                 "OmegaBuild.Plan": {"OmegaBuild.Commands", "Mathlib.Lean.Expr.Basic"},
                 "OmegaChecks.Other": {"Mathlib.Topology.Basic"}}
        def import_graph(lean, *, official_basis=False):
            return ({}, {"OmegaInit": graph["OmegaInit"]} if official_basis
                    else {**graph, "OmegaInit": {"Unexpected.StrictOnly"}})

        upstream.import_graph.side_effect = import_graph
        upstream.closure.return_value = [name for name in graph if name != "OmegaChecks.Other"]
        with tempfile.TemporaryDirectory() as temporary, patch.object(consumer.subprocess, "run") as run:
            upstream.ROOT = Path(temporary)
            config = upstream.ROOT / "lakefile.toml"
            config.write_text('''[[lean_lib]]
name = "OmegaMath"
globs = ["OmegaMath.*"]
[[lean_lib]]
name = "OmegaMathlib"
[[lean_lib]]
name = "OmegaInit"
[[lean_lib]]
name = "OmegaBuild"
roots = ["OmegaBuild.Commands"]
[[lean_exe]]
name = "omegaBackendPlan"
root = "OmegaBuild.Plan"
''')
            consumer.verify_release(adapter, "lean")
            self.assertEqual(upstream.import_graph.call_args_list, [call("lean"), call("lean", official_basis=True)])
            upstream.closure.assert_called_once_with(graph, {"OmegaMath", "OmegaMath.Core", "OmegaMath.Extra",
                                                            "OmegaMathlib", "OmegaInit", "OmegaBuild.Commands",
                                                            "OmegaBuild.Plan"})
            expected = [call(["lake", "exe", "cache", "get", "Batteries.Data.List.Basic", "Mathlib.Algebra.Group.Basic",
                              "Mathlib.Algebra.Ring.Basic", "Mathlib.Data.List.Basic", "Mathlib.Data.Nat.Basic",
                              "Mathlib.Init", "Mathlib.Lean.Expr.Basic", "Mathlib.Tactic.Basic"],
                             cwd=consumer.ROOT, check=True),
                        call(["make", "verify-omegamath-release"], cwd=consumer.ROOT, check=True)]
            self.assertEqual(run.call_args_list, expected)
            run.reset_mock()
            run.side_effect = subprocess.CalledProcessError(1, "lake")
            with self.assertRaises(subprocess.CalledProcessError):
                consumer.verify_release(adapter, "lean")
            self.assertEqual(run.call_args_list, expected[:1])
            run.reset_mock()
            config.write_text(config.read_text().replace('name = "omegaBackendPlan"', 'name = "other"'))
            with self.assertRaises(ValueError):
                consumer.verify_release(adapter, "lean")
            run.assert_not_called()

    def test_receipt_only_scope_runs_real_gate_without_backend_targets(self):
        adapter = Mock()
        adapter.import_graph.return_value = ({}, self.graph)
        adapter.consumers.return_value = self.eligible
        with tempfile.TemporaryDirectory() as temporary, patch.object(consumer, "portable_adapter", return_value=(adapter, "lean")):
            root = Path(temporary)
            changed, scope, targets = (root / name for name in ("changed", "scope", "targets"))
            changed.write_bytes(b"Meta/omegamath-release.json\0")
            with patch.dict(os.environ, {"CI_CHANGED_PATHS_FILE": str(changed)}, clear=True):
                with patch.object(sys, "argv", ["omega-consumer.py", "--write-scope", str(scope), "--cache-targets", str(targets)]):
                    consumer.main()
                self.assertEqual(json.loads(scope.read_text()), {"consumers": [], "verify_release": True})
                self.assertEqual(targets.read_text(), "")
                with patch.dict(os.environ, {"OMEGA_SCOPE_FILE": str(scope)}), patch.object(sys, "argv", ["omega-consumer.py"]), \
                     patch.object(consumer, "verify_release") as verifier:
                    consumer.main()
                verifier.assert_called_once_with(adapter, "lean")
                adapter.check.assert_not_called()

    def test_empty_scope_does_not_call_adapter_and_invalid_scope_fails(self):
        adapter = Mock()
        consumer.check([], adapter)
        adapter.check.assert_not_called()
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "scope"
            for value in (["OmegaMath.Base"], ["D5.Direct", "D5.Direct"], ["Reg.Z", "D5.A"], "D5.A"):
                path.write_text(json.dumps({"consumers": value, "verify_release": False}))
                with self.assertRaisesRegex(ValueError, "invalid downstream consumer scope"):
                    consumer.load_scope(path)


if __name__ == "__main__":
    unittest.main()
