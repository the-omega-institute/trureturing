"""Regression fixtures for affected Omega targets."""
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import check
import scope
from check import library_backend_candidates


class ScopeTests(unittest.TestCase):
    graph = {
        "OmegaInit.Core": set(),
        "OmegaMathlib.Fib": {"OmegaInit.Core"},
        "OmegaMath.Independent": {"OmegaInit.Core"},
        "D5.Direct": {"OmegaMathlib.Fib"},
        "D5.Downstream": {"D5.Direct"},
        "Reg.Observation": {"D5.Downstream"},
        "Reg.Independent": {"OmegaMath.Independent"},
        "D5.Ordinary": set(),
        "OmegaChecks.Portable.Common": {"OmegaMathlib.Fib"},
    }
    official = {"OmegaInit.Core": set(), "OmegaMathlib.Fib": {"OmegaInit.Core", "Mathlib.Fib"}}

    def test_port_selects_direct_and_transitive_consumers_and_common(self):
        plan = scope.plan(self.graph, self.official, {"OmegaMathlib.Fib"}, set(), [], [])
        self.assertEqual(plan["library"], ["OmegaChecks.Portable.Common", "OmegaMathlib.Fib"])
        self.assertEqual(plan["consumers"], ["D5.Direct", "D5.Downstream", "OmegaChecks.Portable.Common",
                                             "Reg.Observation"])
        self.assertEqual(plan["common"], ["OmegaChecks.Portable.Common", "OmegaMathlib.Fib"])
        self.assertEqual(set(scope.cache_targets(plan)), set(plan["library"] + plan["consumers"]) |
                         {scope.AUDIT, scope.CERTIFICATE} | scope.IMPORTER_INPUTS)

    def test_project_and_shared_inputs_select_their_dependents(self):
        for changed, shared, reg_inputs, expected in [
            ({"D5.Direct"}, [], [], ["D5.Direct", "D5.Downstream", "Reg.Observation"]),
            ({"OmegaInit.Core"}, [], [], sorted({"D5.Direct", "D5.Downstream", "OmegaMath.Independent",
                                                "OmegaChecks.Portable.Common", "Reg.Independent", "Reg.Observation"})),
            ({"D5.Ordinary"}, [], ["Reg/lakefile.toml"], ["Reg.Independent", "Reg.Observation"]),
            (set(), ["lean-toolchain"], [], sorted({"D5.Direct", "D5.Downstream", "OmegaMath.Independent",
                                                   "OmegaChecks.Portable.Common", "Reg.Independent", "Reg.Observation"})),
        ]:
            with self.subTest(changed=changed, shared=shared, reg_inputs=reg_inputs):
                plan = scope.plan(self.graph, self.official, changed, set(), shared, reg_inputs)
                self.assertEqual(plan["consumers"], expected)
                self.assertEqual(plan["shared"], shared)

    def test_ordinary_importer_runs_when_either_input_is_affected(self):
        graph = dict(self.graph, OmegaMath=set())
        for name in scope.IMPORTER_INPUTS | {"D5.Direct"}:
            with self.subTest(name=name):
                plan = scope.plan(graph, self.official, {name}, set(), [], [])
                self.assertEqual(scope.importer_affected(plan), name in scope.IMPORTER_INPUTS)
                self.assertEqual(scope.IMPORTER_INPUTS <= set(scope.cache_targets(plan)),
                                 name in scope.IMPORTER_INPUTS)

    def test_official_import_edge_affects_port_and_its_clients(self):
        official = dict(self.official, **{"OmegaMathlib.Fib": {"D5.Ordinary"}})
        plan = scope.plan(self.graph, official, {"D5.Ordinary"}, set(), [], [])
        self.assertIn("D5.Direct", plan["consumers"])

    def test_helper_edit_selects_standalone_publication_leaves(self):
        helper = scope.module_path("src/Shared/Helper.lean")
        self.assertEqual(helper, "Shared.Helper")
        graph = {**self.graph, helper: set(), "OmegaMath.Standalone": {helper},
                 "OmegaMathlib.Standalone": set()}
        official = {**self.official, "OmegaMathlib.Standalone": {helper}}
        plan = scope.plan(graph, official, {helper}, set(), [], [])
        self.assertEqual(plan["library"], ["OmegaMath.Standalone", "OmegaMathlib.Standalone"])
        self.assertEqual(plan["basis"], ["OmegaMathlib.Standalone"])
        self.assertIn("OmegaMath.Standalone", plan["consumers"])

    def test_library_and_scoped_admission_check_a_standalone_module_on_both_backends(self):
        leaf = "OmegaMath.Standalone"
        graph = {**self.graph, leaf: {"OmegaMathlib.Fib"}}
        plan = scope.plan(graph, self.official, {leaf}, set(), [], [])
        with patch.object(check, "run"), patch.object(check, "lake_environment", return_value={}), \
                patch.object(check, "library_graph", return_value=graph), \
                patch.object(check, "check_library", return_value=["OmegaMathlib.Fib", leaf]), \
                patch.object(check.portable, "check") as portable:
            check.check_selected_library([leaf])
            portable.assert_called_once_with([leaf], "both", basis_roots=[])
            portable.reset_mock()
            check.scoped_check(plan)
            portable.assert_called_once_with([leaf], "both", basis_roots=[], common_roots=[])

    def test_missing_protected_base_fails_local_admission(self):
        with TemporaryDirectory() as directory:
            env = {k: v for k, v in os.environ.items() if k not in {"CI", "CI_BASE"}}
            result = subprocess.run([sys.executable, "-B", Path(check.__file__), "--library", "OmegaMath"],
                                    env={**env, "GIT_DIR": directory}, text=True, capture_output=True)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn("requires --protected-base or CI_BASE", result.stderr)

    def test_backend_command_inputs_and_ordinary_marked_module_reach_scope(self):
        for path in ("src/OmegaBuild/Commands.lean", "src/OmegaBuild/Plan.lean"):
            name = scope.module_path(path)
            self.assertIn(name, scope.CHECK_INPUTS)
            plan = scope.plan({**self.graph, name: set()}, self.official, {name}, set(), [], [])
            self.assertEqual(plan["shared"], [name])
            self.assertNotIn(name, plan["library"])
        graph = {**self.graph, "OmegaBuild.Commands": set(),
                 "D5.Markable": {"OmegaBuild.Commands"}, "Reg.Inherited": {"D5.Markable"}}
        result = scope.plan(graph, self.official, {"D5.Markable"}, set(), [], [])
        self.assertEqual(result["consumers"], ["D5.Markable", "Reg.Inherited"])

    def test_publication_rejects_an_official_only_module_or_dependency(self):
        for prefix in ("OmegaMath", "OmegaMathlib", "OmegaInit"):
            name = prefix + ".Marked"
            for chain in ([name], [name, "Support.Marked"]):
                report = {"mathlibOnly": {name: chain}, "declarations": []}
                with self.subTest(chain=chain), patch.object(check.portable.subprocess, "run"), \
                        patch.object(check.portable, "output", return_value=json.dumps(report)), \
                        self.assertRaisesRegex(RuntimeError, "publication requires both backends") as error:
                    check.portable.backend_plan("test-path", [name])
                self.assertIn(" -> ".join(chain), str(error.exception))

    def test_official_plan_includes_every_publication_and_witnesses_that_can_use_a_marker(self):
        graph = {"OmegaBuild.Commands": set(), "OmegaInit.Base": set(), "OmegaMathlib.Base": set(),
                 "OmegaMath.Base": set(),
                 "OmegaMath.Optional": {"OmegaBuild.Commands"},
                 "OmegaChecks.Mixed": {"OmegaMath.Base"},
                 "OmegaChecks.Optional": {"OmegaMath.Optional"},
                 "D5.Marked": {"OmegaBuild.Commands"},
                 "Trureturing": {"D5.Marked"}, "OmegaChecks.D5Witness": {"Trureturing"}}
        self.assertEqual(library_backend_candidates(graph, graph),
                         ["OmegaInit.Base", "OmegaMathlib.Base", "OmegaMath.Base", "OmegaMath.Optional",
                          "OmegaChecks.Optional", "D5.Marked", "Trureturing", "OmegaChecks.D5Witness"])

    def test_full_and_incremental_probes_schedule_only_eligible_strict_roots(self):
        graph = {"OmegaMath.Base": set(), "OmegaChecks.Marked": {"OmegaMath.Base"},
                 "OmegaChecks.Inherited": {"OmegaChecks.Marked"}, "OmegaChecks.Sibling": {"OmegaMath.Base"}}
        skipped = {"OmegaChecks.Marked": ["OmegaChecks.Marked"],
                   "OmegaChecks.Inherited": ["OmegaChecks.Inherited", "OmegaChecks.Marked"]}
        with patch.object(check, "library_graph", return_value=graph), \
             patch.object(check, "library_mathlib_only", return_value=skipped):
            for entry in (check.check_library, check.check_incremental):
                with self.subTest(entry=entry), patch.object(check, "build", side_effect=StopIteration) as build:
                    # Stop at the first build request, before probes modify files or run the auditor.
                    with self.assertRaises(StopIteration):
                        entry()
                    build.assert_called_once_with(["OmegaChecks.Sibling"])

    def test_current_builds_backend_programs_officially_and_tests_mixed_selections(self):
        graph = {"OmegaBuild.Commands": set(), "OmegaBuild.Plan": {"OmegaBuild.Commands"},
                 "OmegaChecks.Witness": set()}
        with patch.object(check, "library_graph", return_value=graph), \
             patch.object(check, "run") as official, patch.object(check, "build") as strict:
            check.check_library(["OmegaBuild.Commands", "OmegaBuild.Plan"])
            official.assert_called_once_with("lake", "build", "+OmegaBuild.Plan")
            strict.assert_not_called()
            check.check_library(["OmegaBuild.Commands", "OmegaBuild.Plan", "OmegaChecks.Witness"])
            strict.assert_called_once_with(["OmegaChecks.Witness"])
            with self.assertRaisesRegex(ValueError, "unknown Omega module"):
                check.check_library(["OmegaBuild.Typo"])

    def test_deletions_preserve_errors_for_surviving_imports_and_required_inputs(self):
        for missing in ({"D5.Direct"}, {scope.CERTIFICATE}):
            with self.subTest(missing=missing), self.assertRaisesRegex(ValueError, "still required"):
                scope.plan(self.graph, self.official, missing, missing, [], [])
        with self.assertRaisesRegex(ValueError, "module trees differ"):
            scope.plan(self.graph, {"OmegaInit.Core": set()}, set(), set(), [], [])
        removed = {"D5.Removed"}
        plan = scope.plan(self.graph, self.official, removed, removed, [], [])
        self.assertEqual(scope.cache_targets(plan), [])
        self.assertEqual(scope.report_file(plan), "")

    def test_empty_unrelated_and_missing_changed_manifests(self):
        with TemporaryDirectory() as temporary:
            paths = Path(temporary) / "changed"
            with self.assertRaises(FileNotFoundError):
                scope.discover(paths)
            for content in (b"", b"README.md\0"):
                paths.write_bytes(content)
                plan = scope.discover(paths)
                self.assertEqual(scope.cache_targets(plan), [])
                self.assertEqual(scope.report_file(plan), "")
            paths.write_bytes(b"D5/Unterminated.lean")
            with self.assertRaisesRegex(ValueError, "NUL-separated"):
                scope.discover(paths)


if __name__ == "__main__":
    unittest.main()
