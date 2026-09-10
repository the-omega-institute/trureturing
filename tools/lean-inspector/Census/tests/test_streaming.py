"""Streaming census contracts: scope, ownership, freshness, and actual replay."""

import copy
import json
import pathlib
import tempfile
import unittest
from unittest import mock


class StreamingTests(unittest.TestCase):
    def test_domain_follows_lakes_default_library_globs(self):
        from streaming import tracked_domain
        config = {"defaultTargets": ["Project", "Inspector"], "lean_lib": [
            {"name": "Project", "globs": ["D5.+"]},
            {"name": "Inspector", "srcDir": "tools/lean-inspector", "globs": ["Inspector.+"]},
            {"name": "OptIn", "srcDir": "tools/lean-inspector", "globs": ["Analysis.+"]}]}
        paths = b"D5/A.lean\0tools/lean-inspector/Inspector/B.lean\0tools/lean-inspector/Analysis/C.lean\0"
        with mock.patch("streaming.subprocess.check_output", side_effect=[paths, json.dumps(config)]):
            self.assertEqual(tracked_domain("/fixture"), {
                "D5.A": "D5/A.lean", "Inspector.B": "tools/lean-inspector/Inspector/B.lean"})

    def test_freshness_gate_propagates_lake_failure(self):
        from streaming import freshness
        calls = []

        def build(command, label):
            calls.append((command, label))
            raise RuntimeError("stale fixture: lake rejected edited source")

        with self.assertRaisesRegex(RuntimeError, "stale fixture"):
            freshness(build)
        self.assertEqual(calls, [(["make", "lean"], "lake_freshness")])

    def test_missing_olean_fails_closed_and_untracked_cache_is_ignored(self):
        from streaming import check_domain
        with self.assertRaisesRegex(ValueError, "missing.*Fixture.B"):
            check_domain({"Fixture.A", "Fixture.B"}, {"Fixture.A"})
        check_domain({"Fixture.A"}, {"Fixture.A", "Fixture.B"})
        check_domain({"Fixture.A"}, {"Fixture.A"})

    def test_ownership_collision_is_a_row_error(self):
        from streaming import owner_error
        records = [{"module": "Fixture.A", "matches": True},
                   {"module": "Fixture.B", "matches": True}]
        self.assertIn("IE-C035", owner_error("Fixture.B", records))
        self.assertIsNone(owner_error("Fixture.B", records[1:]))

    def test_ownership_uses_membership_not_first_import(self):
        from streaming import owner_error
        records = [{"module": "Fixture.Second", "matches": True,
                    "first_import": "Fixture.First"}]
        self.assertIsNone(owner_error("Fixture.Second", records))
        records[0]["matches"] = False
        self.assertIn("IE-C036", owner_error("Fixture.Second", records))
        self.assertIn("IE-C034", owner_error("Fixture.Absent", []))

    def test_unclassifiable_named_key_is_never_absent(self):
        from streaming import select_candidates
        named = [{"module": "Fixture.Evidence", "head": "keyed",
                  "key": None, "name": "opaqueKeyEvidence"}]
        hits, error = select_candidates("key", {"Fixture.Evidence"}, [], named)
        self.assertIn("IE-C036", error)
        self.assertEqual(hits, [])

    def test_out_of_scope_evidence_cannot_certify(self):
        from streaming import select_candidates
        entry = {"module": "Fixture.Outside", "key": "key", "name": "validEvidence"}
        hits, error = select_candidates("key", {"Fixture.Source"}, [entry], [])
        self.assertEqual((hits, error), ([], None))
        self.assertEqual(select_candidates("key", {"Fixture.Source", "Fixture.Outside"},
                                           [entry], [])[0], [entry])

    def test_root_scope_keeps_peer_and_discovered_evidence(self):
        from streaming import closure, root_scopes
        graph = {"D5.S0.Area.A": ["Init"], "D5.S0.Area.B": ["Init"],
                 "Evidence": ["D5.S0.Area.A"], "Init": [],
                 "LeanInformationAudit.Census.Command": ["Init"]}
        keys = [("D5.S0.Area.A", "a", "id-a"), ("D5.S0.Area.B", "b", "id-b")]
        roots, assignment = root_scopes([key[0] for key in keys], keys, ["Evidence"], graph)
        scope = set(roots[assignment["D5.S0.Area.A"]])
        self.assertIn("D5.S0.Area.B", scope)
        self.assertIn("Evidence", scope)
        self.assertNotIn("Evidence", closure(graph, ["D5.S0.Area.A"]))

    def test_receipt_digest_includes_import_graph(self):
        from streaming import receipt_digest
        value = {"head": "head", "oleans": [], "import_graph": {"A": ["B"], "B": []},
                 "programs": [], "export_sha256": "export", "domain": ["A"],
                 "scopes": {"Root": ["A", "B"]}, "toolchain": "fixture"}
        changed = copy.deepcopy(value)
        changed["import_graph"]["A"] = []
        self.assertNotEqual(receipt_digest(value), receipt_digest(changed))

    def test_replay_rereads_recomputes_and_revalidates(self):
        from streaming import replay
        calls = []

        def scan():
            calls.extend(["enumerate", "read", "graph", "membership", "validate"])
            return {"rows": [1], "receipt": "digest"}

        self.assertEqual(replay(scan, {"rows": [1], "receipt": "digest"}), "match")
        self.assertEqual(calls, ["enumerate", "read", "graph", "membership", "validate"])
        with self.assertRaisesRegex(ValueError, "replay mismatch"):
            replay(scan, {"rows": [2], "receipt": "digest"})

    def test_replay_changed_olean_byte_is_red(self):
        from streaming import hash_inputs, replay
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder) / "Fixture.olean"
            path.write_bytes(b"original olean bytes")

            def scan():
                return hash_inputs([("Fixture", "base", str(path))])

            before = scan()
            path.write_bytes(b"Original olean bytes")
            with self.assertRaisesRegex(ValueError, "replay mismatch"):
                replay(scan, before)


if __name__ == "__main__":
    unittest.main()
