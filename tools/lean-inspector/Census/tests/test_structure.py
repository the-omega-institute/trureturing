"""The panel's structural reading contract; no assessment classifications."""

import json
import pathlib
import tempfile
import unittest

from negative_fixtures import name_key


def key(name, module="Fixture", identity=None):
    return (module, name_key(name), identity or "id-" + module + "-" + name)


class StructureTests(unittest.TestCase):
    def setUp(self):
        from Structure.store import Store
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.path = pathlib.Path(self.scratch.name)
        self.store = Store(self.path / "raw.sqlite")
        self.addCleanup(self.store.close)
        self.store.module("Core", [], "Init")
        self.store.module("Fixture", ["Core"], "repository")
        for name in ("True.intro", "Eq.mpr", "Eq.refl", "Nat.succ", "Nat.rec"):
            self.decl(name, [], module="Core", kind="other")

    def decl(self, name, value, types=(), module="Fixture", kind="theorem"):
        self.store.declaration(module, name_key(name), kind,
                               None if value is None else [name_key(n) for n in value],
                               [name_key(n) for n in types])

    def run_graph(self, keys, core=("True.intro", "Eq.mpr", "Eq.refl"), cache=None):
        from Structure.graph import analyse
        result = self.path / "rows.jsonl"
        summary = analyse(self.store, keys, result, [name_key(n) for n in core],
                          cache=cache, axioms={(k[1], k[2]): [] for k in keys})
        rows = [json.loads(line) for line in result.read_text().splitlines()]
        return {r["statement_id"]: r for r in rows}, summary

    def reading(self, rows, name, module="Fixture"):
        return rows[key(name, module)[2]]["readings"]

    def panel(self):
        self.decl("a", [])
        self.decl("h", ["a"], kind="def")
        self.decl("b", ["h"])
        self.decl("c", ["a"])
        self.decl("d", ["b", "c"])
        self.decl("g", ["b"])
        return [key(n) for n in "abcdg"]

    def test_panel_direct_folded_depth_and_distinct_descendants(self):
        rows, summary = self.run_graph(self.panel())
        direct = {"a": [], "b": [], "c": ["a"], "d": ["b", "c"], "g": ["b"]}
        folded = dict(direct, b=["a"])
        for n, depth, descendants in zip("abcdg", [0, 1, 1, 2, 2], [4, 2, 1, 0, 0]):
            reading = self.reading(rows, n)
            for field, expected in [("direct_frozen_prerequisites", direct),
                                    ("folded_frozen_prerequisites", folded)]:
                self.assertEqual([r["statement_id"] for r in reading[field]], [key(x)[2] for x in expected[n]])
            self.assertEqual(reading["frozen_dag_depth"], depth)
            self.assertEqual(reading["descendant_subgraph_size"], descendants)
        self.assertEqual(summary["direct_depths"], {key(n)[2]: d for n, d in zip("abcdg", [0, 0, 1, 2, 1])})
        self.assertEqual((summary["direct_edges"], summary["folded_edges"]), (4, 5))

    def test_helper_alias_and_substantive_helper_both_fold(self):
        self.decl("a", [])
        self.decl("alias", ["a"], kind="def")
        self.decl("substantive", ["a", "Nat.succ"], kind="def")
        self.decl("b", ["alias"])
        self.decl("c", ["substantive"])
        rows, _ = self.run_graph([key(n) for n in "abc"])
        for n in "bc":
            self.assertEqual(self.reading(rows, n)["folded_frozen_prerequisites"][0]["statement_id"], key("a")[2])
            self.assertEqual(self.reading(rows, n)["core_or_frozen_support"], "undetermined")
        self.assertEqual(self.reading(rows, "c")["upstream_boundary_constants"][0]["library"], "Init")

    def test_supplied_equality_vs_new_equality_and_local_instance(self):
        self.decl("equality", ["Eq.refl"])
        self.decl("supplied", ["Eq.mpr", "equality"])
        self.decl("newEquality", ["Eq.mpr", "Nat.rec"])
        self.decl("instance", ["equality"], kind="def")
        self.decl("localInstance", ["instance"])
        rows, _ = self.run_graph([key(n) for n in ["equality", "supplied", "newEquality", "localInstance"]])
        self.assertIs(self.reading(rows, "supplied")["core_or_frozen_support"], True)
        self.assertEqual(self.reading(rows, "newEquality")["core_or_frozen_support"], "undetermined")
        self.assertEqual(self.reading(rows, "localInstance")["folded_frozen_prerequisites"][0]["statement_id"], key("equality")[2])

    def test_nat_and_core_namespace_are_not_support_whitelists(self):
        self.decl("True.substantive", [], module="Core", kind="other")
        self.decl("a", ["Nat.succ"])
        self.decl("b", ["True.substantive"])
        rows, _ = self.run_graph([key("a"), key("b")])
        for n in "ab":
            self.assertEqual(self.reading(rows, n)["core_or_frozen_support"], "undetermined")

    def test_collision_uses_full_key_and_import_scope(self):
        for module in ["Left", "Right"]:
            self.store.module(module, ["Core"], "repository")
            self.decl("shared.congr_simp", [], module=module)
        self.store.module("Fixture", ["Left", "Right"], "repository")
        self.decl("a", ["shared.congr_simp"])
        keys = [key("shared.congr_simp", m) for m in ["Left", "Right"]] + [key("a")]
        rows, _ = self.run_graph(keys)
        self.assertEqual(len(rows), 3)
        self.assertEqual(rows[key("a")[2]].get("reason"), "frozen_key_ambiguous")
        self.assertIsNone(rows[key("a")[2]]["readings"])
        self.store.module("Fixture", ["Left"], "repository")
        rows, _ = self.run_graph(keys)
        self.assertEqual(self.reading(rows, "a")["direct_frozen_prerequisites"][0]["statement_id"], keys[0][2])

    def test_failed_extraction_is_unavailable_never_empty(self):
        self.decl("privateBody", None, kind="opaque")
        self.decl("a", ["privateBody"])
        rows, _ = self.run_graph([key("a")])
        self.assertEqual(rows[key("a")[2]]["status"], "unavailable")
        self.assertEqual(rows[key("a")[2]]["reason"], "value_unavailable")
        self.assertIsNone(rows[key("a")[2]]["readings"])

    def test_missing_kind_and_unresolved_reasons_are_closed(self):
        self.decl("wrong", [], kind="def")
        self.decl("missingRef", ["doesNotExist"])
        rows, _ = self.run_graph([key(n) for n in ["absent", "wrong", "missingRef"]])
        for n, reason in [("absent", "constant_missing"), ("wrong", "kind_mismatch"),
                          ("missingRef", "dependency_unresolved")]:
            self.assertEqual(rows[key(n)[2]]["reason"], reason)
            self.assertIsNone(rows[key(n)[2]]["readings"])

    def test_sorry_and_repository_axiom_are_readable(self):
        self.decl("sorryAx", None, module="Core", kind="axiom")
        self.decl("ownAxiom", None, kind="axiom")
        self.decl("a", ["sorryAx", "ownAxiom"])
        rows, _ = self.run_graph([key("a")])
        self.assertEqual(rows[key("a")[2]]["status"], "complete")
        self.assertEqual(self.reading(rows, "a")["core_or_frozen_support"], "undetermined")

    def test_non_frozen_scc_closes_together(self):
        self.decl("a", [])
        self.decl("h", ["j", "a"], kind="def")
        self.decl("j", ["h"], kind="def")
        self.decl("b", ["j"])
        rows, _ = self.run_graph([key("a"), key("b")])
        self.assertEqual(self.reading(rows, "b")["frozen_dag_depth"], 1)

    def test_projected_cycle_and_self_edge_are_unavailable(self):
        self.decl("a", ["b"])
        self.decl("b", ["a"])
        self.decl("c", ["c"])
        rows, summary = self.run_graph([key(n) for n in "abc"])
        for row in rows.values():
            self.assertEqual((row["status"], row["reason"], row["readings"]), ("unavailable", "graph_cycle", None))
        self.assertEqual(summary["folded_edges"], 3)
        self.assertEqual(summary["self_edges"], [key("c")[2]])

    def test_newly_frozen_helper_invalidates_unchanged_raw_cache(self):
        keys = self.panel()
        cache = self.path / "cache"
        first, _ = self.run_graph(keys, cache=cache)
        # A theorem helper can become frozen without changing its proof bytes.
        self.decl("h", ["a"])
        self.run_graph(keys, cache=cache)
        second, _ = self.run_graph(keys + [key("h")], cache=cache)
        self.assertEqual(self.reading(first, "b")["folded_frozen_prerequisites"][0]["statement_id"], key("a")[2])
        self.assertEqual(self.reading(second, "b")["folded_frozen_prerequisites"][0]["statement_id"], key("h")[2])
        self.assertEqual(self.reading(second, "b")["frozen_dag_depth"], 2)

    def test_type_constants_are_not_direct_seeds(self):
        self.decl("a", [])
        self.decl("b", ["True.intro"], types=["a"])
        rows, _ = self.run_graph([key("a"), key("b")])
        self.assertEqual(self.reading(rows, "b")["direct_frozen_prerequisites"], [])
        self.assertEqual(self.reading(rows, "b")["value_constant_count"], 1)

    def test_cache_tracks_helper_body_and_root_read_error(self):
        keys = self.panel()
        cache = self.path / "cache"
        self.run_graph(keys, cache=cache)
        self.decl("h", ["c"], kind="def")
        rows, summary = self.run_graph(keys, cache=cache)
        self.assertEqual(self.reading(rows, "b")["folded_frozen_prerequisites"][0]["statement_id"], key("c")[2])
        self.assertGreater(summary["cache"]["fold_hits"], 0)
        self.store.module("Fixture", ["Core"], "repository", error="missing_olean_part")
        rows, _ = self.run_graph(keys, cache=cache)
        self.assertEqual(rows[key("a")[2]]["reason"], "missing_olean_part")

    def test_unresolved_extraction_propagates_missing_graph_fields(self):
        self.decl("a", [])
        self.decl("b", ["absent"])
        self.decl("c", ["b"])
        rows, _ = self.run_graph([key(n) for n in "abc"])
        self.assertEqual(rows[key("c")[2]]["status"], "partial")
        self.assertEqual(rows[key("c")[2]]["missing_fields"], ["descendant_subgraph_size", "frozen_dag_depth"])
        self.assertEqual(self.reading(rows, "a")["frozen_dag_depth"], 0)
        self.assertIsNone(self.reading(rows, "a")["descendant_subgraph_size"])

    def test_upstream_name_collisions_preserve_all_provenance(self):
        self.store.module("OtherCore", [], "Init")
        self.decl("True.intro", [], module="OtherCore", kind="other")
        self.store.module("Fixture", ["Core", "OtherCore"], "repository")
        self.decl("a", ["True.intro"])
        rows, _ = self.run_graph([key("a")])
        boundary = self.reading(rows, "a")["upstream_boundary_constants"]
        self.assertEqual(boundary[0]["provenance"], [
            {"declaring_module": "Core", "library": "Init"},
            {"declaring_module": "OtherCore", "library": "Init"}])

    def test_ambiguous_helpers_bound_only_their_possible_descendants(self):
        self.store.module("Base", ["Core"], "repository")
        for name in "ab":
            self.decl(name, [], module="Base")
        for module, target in [("Left", "a"), ("Right", "b")]:
            self.store.module(module, ["Base"], "repository")
            self.decl("h", [target], module=module, kind="def")
        self.store.module("Fixture", ["Left", "Right"], "repository")
        self.decl("c", ["h"])
        self.decl("d", [])
        self.decl("e", ["c"])
        keys = [key(n, "Base") for n in "ab"] + [key(n) for n in "cde"]
        rows, _ = self.run_graph(keys)
        self.assertIsNone(rows[key("c")[2]]["readings"])
        self.assertEqual(rows[key("c")[2]]["reason"], "dependency_unresolved")
        self.assertEqual(rows[key("d")[2]]["status"], "complete")
        self.assertEqual(self.reading(rows, "d")["descendant_subgraph_size"], 0)
        for n in "ab":
            self.assertIsNone(self.reading(rows, n, "Base")["descendant_subgraph_size"])
        self.assertIsNone(self.reading(rows, "e")["frozen_dag_depth"])


if __name__ == "__main__":
    unittest.main()
