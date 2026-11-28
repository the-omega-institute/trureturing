"""Selection and dispatch tests with a mocked portable adapter."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

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
            scope, selected_adapter, discovered = consumer.discover(manifest)
            names = scope["consumers"]
            self.assertFalse(scope["verify_release"])
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
                    scope, _, _ = consumer.discover(path)
                    self.assertTrue(scope["verify_release"])
            scope, _, _ = consumer.discover(None)
            self.assertTrue(scope["verify_release"])
            path.write_bytes(b"")
            scope, _, _ = consumer.discover(path)
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

    def test_receipt_only_scope_runs_just_the_release_verifier(self):
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(consumer, "portable_adapter") as load_adapter, \
             patch.object(consumer.subprocess, "run") as run:
            root = Path(temporary)
            changed, scope, targets = (root / name for name in ("changed", "scope", "targets"))
            changed.write_bytes(b"Meta/omegamath-release.json\0")
            with patch.dict(os.environ, {"CI_CHANGED_PATHS_FILE": str(changed)}, clear=True):
                with patch.object(sys, "argv", ["omega-consumer.py", "--write-scope", str(scope), "--cache-targets", str(targets)]):
                    consumer.main()
                self.assertEqual(json.loads(scope.read_text()), {"consumers": [], "verify_release": True})
                self.assertEqual(targets.read_text(), "")
                run.assert_not_called()
                with patch.dict(os.environ, {"OMEGA_SCOPE_FILE": str(scope)}), patch.object(sys, "argv", ["omega-consumer.py"]):
                    consumer.main()
                run.assert_called_once_with(["make", "verify-omegamath-release"], cwd=consumer.ROOT, check=True)
                load_adapter.assert_not_called()

    def test_release_and_backend_checks_run_in_order_and_propagate_release_failure(self):
        adapter = Mock()
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(consumer, "portable_adapter", return_value=(adapter, "lean")) as load_adapter, \
             patch.object(consumer.subprocess, "run") as run:
            scope = Path(temporary) / "scope"
            names = ["D5.Direct", "Reg.Observation"]
            scope.write_text(json.dumps({"consumers": names, "verify_release": True}))
            with patch.dict(os.environ, {"OMEGA_SCOPE_FILE": str(scope)}, clear=True), patch.object(sys, "argv", ["omega-consumer.py"]):
                failure = subprocess.CalledProcessError(1, "make")
                run.side_effect = failure
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    consumer.main()
                self.assertIs(error.exception, failure)
                load_adapter.assert_not_called()
                adapter.check.assert_not_called()
                run.assert_called_once_with(["make", "verify-omegamath-release"], cwd=consumer.ROOT, check=True)
                run.reset_mock()
                run.side_effect = None
                adapter.check.side_effect = lambda *args, **kwargs: run.assert_called_once_with(
                    ["make", "verify-omegamath-release"], cwd=consumer.ROOT, check=True)
                consumer.main()
                adapter.check.assert_called_once_with(names, "both", basis_roots=[], common_roots=(), discovered=None)

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
