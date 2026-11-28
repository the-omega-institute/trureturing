"""Regression fixtures for affected Omega targets."""
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import scope
import check
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

    def test_dependency_closure_order_is_stable_across_processes(self):
        program = ("from portable import closure\n"
                   "graph = {'A': {'B', 'C', 'D'}, 'B': set(), 'C': set(), 'D': set()}\n"
                   "print(*closure(graph, ['A']))")
        for seed in ("0", "1", "2"):
            with self.subTest(seed=seed):
                order = subprocess.check_output([sys.executable, "-B", "-c", program], text=True,
                                                cwd=Path(__file__).parent, env={**os.environ, "PYTHONHASHSEED": seed})
                self.assertEqual(order.split(), ["B", "C", "D", "A"])

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

    def test_strict_witnesses_are_resolved_officially_only_if_they_can_use_a_marker(self):
        graph = {"OmegaBuild.Commands": set(), "OmegaMath.Base": set(),
                 "OmegaMath.Optional": {"OmegaBuild.Commands"},
                 "OmegaChecks.Mixed": {"OmegaMath.Base"},
                 "OmegaChecks.Optional": {"OmegaMath.Optional"},
                 "D5.Marked": {"OmegaBuild.Commands"},
                 "Trureturing": {"D5.Marked"}, "OmegaChecks.D5Witness": {"Trureturing"}}
        self.assertEqual(library_backend_candidates(graph, graph),
                         ["OmegaMath.Optional", "OmegaChecks.Optional", "D5.Marked", "Trureturing", "OmegaChecks.D5Witness"])

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
