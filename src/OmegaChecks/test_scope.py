"""Regression fixtures for affected Omega targets."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import scope


class ScopeTests(unittest.TestCase):
    graph = {
        "OmegaInit.Core": set(),
        "OmegaMathlib.Fib": {"OmegaInit.Core"},
        "D5.Independent": {"OmegaInit.Core"},
        "D5.Direct": {"OmegaMathlib.Fib"},
        "D5.Downstream": {"D5.Direct"},
        "Reg.Observation": {"D5.Downstream"},
        "Reg.Independent": {"D5.Independent"},
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
            ({"OmegaInit.Core"}, [], [], sorted({"D5.Direct", "D5.Downstream", "D5.Independent",
                                                "OmegaChecks.Portable.Common", "Reg.Independent", "Reg.Observation"})),
            ({"D5.Ordinary"}, [], ["Reg/lakefile.toml"], ["Reg.Independent", "Reg.Observation"]),
            (set(), ["lean-toolchain"], [], sorted({"D5.Direct", "D5.Downstream", "D5.Independent",
                                                   "OmegaChecks.Portable.Common", "Reg.Independent", "Reg.Observation"})),
        ]:
            with self.subTest(changed=changed, shared=shared, reg_inputs=reg_inputs):
                plan = scope.plan(self.graph, self.official, changed, set(), shared, reg_inputs)
                self.assertEqual(plan["consumers"], expected)
                self.assertEqual(plan["shared"], shared)

    def test_last_port_import_removal_keeps_protected_consumer(self):
        plan = scope.plan(self.graph, self.official, {"D5.Ordinary"}, set(), [], [], {"D5.Ordinary"})
        self.assertIn("D5.Ordinary", plan["consumers"])
        with self.assertRaisesRegex(ValueError, "missing protected publication consumers"):
            scope.plan(self.graph, self.official, set(), set(), [], [], {"D5.Disappeared"})

    def test_unimported_project_publication_is_a_dual_and_frozen_check_root(self):
        graph = dict(self.graph, **{'OmegaMath.Orphan': set(), 'D5.UsesProof': {'OmegaMath.Orphan'}})
        plan = scope.plan(graph, self.official, {'OmegaMath.Orphan'}, set(), [], [])
        self.assertEqual(plan['library'], ['OmegaMath.Orphan'])
        self.assertEqual(plan['consumers'], ['D5.UsesProof', 'OmegaMath.Orphan'])
        self.assertEqual(plan['basis'], [])
        self.assertTrue(scope.report_file(plan))

    def test_ordinary_importer_runs_when_either_input_is_affected(self):
        graph = dict(self.graph, OmegaMathlib=set(), OmegaMath=set())
        for name in scope.IMPORTER_INPUTS | {"D5.Direct"}:
            with self.subTest(name=name):
                plan = scope.plan(graph, dict(self.official, OmegaMathlib=set()), {name}, set(), [], [])
                self.assertEqual(scope.importer_affected(plan), name in scope.IMPORTER_INPUTS)
                self.assertEqual(scope.IMPORTER_INPUTS <= set(scope.cache_targets(plan)),
                                 name in scope.IMPORTER_INPUTS)

    def test_official_import_edge_affects_port_and_its_clients(self):
        official = dict(self.official, **{"OmegaMathlib.Fib": {"D5.Ordinary"}})
        plan = scope.plan(self.graph, official, {"D5.Ordinary"}, set(), [], [])
        self.assertIn("D5.Direct", plan["consumers"])

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
