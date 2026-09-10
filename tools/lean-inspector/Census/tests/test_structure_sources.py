"""Cache input binding, full-key axiom joins and cross-tree artifact bytes."""

import json
import pathlib
import tempfile
import unittest

from negative_fixtures import name_key
from phases import write
from streaming import digest
from Structure.sidecar import axiom_readings, header, publish
from Structure.graph import analyse
from Structure.sources import file_digest, pack, part_plan, split_summaries
from Structure.store import Store


class StructureSourceTests(unittest.TestCase):
    def test_stream_pack_and_part_cache_restore_agree_on_private_override(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            raw = root / "raw.jsonl"
            hashes = [["A", p, 1, p] for p in ["base", "server", "private"]]
            plans = part_plan([["A", ["base", "server", "private"]]], hashes, "reader", root, "bodies")
            records = [
                {"module": "A", "part": "base", "imports": []},
                {"name": name_key("h"), "kind": "opaque", "value": None, "type": []},
                {"module": "A", "part": "server", "imports": []},
                {"module": "A", "part": "private", "imports": []},
                {"name": name_key("h"), "kind": "opaque",
                 "value": [name_key("a")], "type": []}]
            from streaming import canonical
            raw.write_bytes(b"".join(canonical(r) for r in records))
            stores = [Store(root / (n + ".sqlite")) for n in ["stream", "restore"]]
            try:
                stats = split_summaries(raw, plans, stores[0], {"A": "repository"})
                self.assertEqual(stats["stream_packed_modules"], 1)
                pack(stores[1], plans, {"A": "repository"})
                self.assertEqual(stores[0].raw("A", name_key("h")), stores[1].raw("A", name_key("h")))
                self.assertEqual(stores[0].raw("A", name_key("h"))[1], [name_key("a")])
                self.assertEqual(stores[0].snapshot(), stores[1].snapshot())
            finally:
                for store in stores:
                    store.close()

    def test_structured_names_preserve_unicode_and_numeric_components(self):
        from Structure.sources import pack_declaration
        with tempfile.TemporaryDirectory() as scratch:
            store = Store(pathlib.Path(scratch) / "names.sqlite")
            try:
                store.module("A", [], "repository")
                row = {"name": "nn(ns(n0,2:é),7)", "kind": "theorem",
                       "value": ["ns(n0,1:7)"], "type": ["n0"]}
                stats = dict(packed_declarations=0, value_walks=0, type_walks=0,
                             value_name_incidences=0, type_name_incidences=0)
                pack_declaration(store, "A", row, "repository", stats)
                self.assertEqual(store.raw("A", "nn(ns(n0,2:é),7)")[:3],
                                 ("theorem", ["ns(n0,1:7)"], ["n0"]))
            finally:
                store.close()

    def test_part_cache_binds_content_layout_reader_but_not_tree_path(self):
        hashes = [["A", "base", 3, "digest-a"], ["A", "server", 2, "digest-s"]]
        plan = lambda paths, values=hashes, reader="reader": part_plan(
            [["A", paths]], values, reader, pathlib.Path("cache"), "bodies")["A"]["address"]
        first = plan(["one/A.olean", "one/A.olean.server"])
        self.assertEqual(first, plan(["two/A.olean", "two/A.olean.server"]))
        self.assertNotEqual(first, plan(["one/A.olean"]))
        self.assertNotEqual(first, plan(["one/A.olean", "one/A.olean.server"], reader="changed"))
        self.assertNotEqual(first, plan(["one/A.olean", "one/A.olean.server"],
                                       [["A", "base", 3, "new"], hashes[1]]))

    def test_axiom_join_requires_name_identity_owner_and_source(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            source, report = root / "A.lean", root / "report.json"
            source.write_text("fixture source")
            row = {"kind": "theorem", "name_key": name_key("a"), "statement_id": "id-a", "axioms": ["sorryAx"]}
            module = {"module": "A", "source_path": "A.lean", "source_sha256": file_digest(source), "declarations": [row]}
            write(report, {"modules": [module]})
            keys = [("A", name_key("a"), "id-a"), ("A", name_key("a"), "wrong-id"),
                    ("Wrong", name_key("a"), "id-a")]
            self.assertEqual(axiom_readings(root, report, keys), {(name_key("a"), "id-a"): ["sorryAx"]})
            source.write_text("changed")
            self.assertEqual(axiom_readings(root, report, keys), {})

    def test_cross_tree_bytes_equal_with_identical_semantic_inputs(self):
        with tempfile.TemporaryDirectory() as scratch:
            artifacts = []
            for tree in ["left", "right"]:
                root = pathlib.Path(scratch) / tree
                root.mkdir()
                key = ("A", name_key("a"), "id-a")
                write(root / "request.json", {"head": "same-head", "report_sha256": "same-report", "keys": [key]})
                (root / "census.json").write_bytes(b'{"counts":{"observed":1}}\n')
                store = Store(root / "store.sqlite")
                try:
                    store.module("A", [], "repository")
                    store.declaration("A", key[1], "theorem", [])
                    rows = root / "rows.jsonl"
                    analyse(store, [key], rows, [], cache=root / "cache", axioms={key[1:]: []})
                    inputs = {"olean_part_manifest_sha256": digest([]), "reader_fingerprint": "same-reader",
                              "ownership_fingerprint": store.snapshot()}
                    publish(root, header(root, inputs), rows)
                finally:
                    store.close()
                artifacts.append((root / "census-structure.json").read_bytes())
            self.assertEqual(*artifacts)
            self.assertEqual(json.loads(artifacts[0])["rows"][0]["status"], "complete")


if __name__ == "__main__":
    unittest.main()
