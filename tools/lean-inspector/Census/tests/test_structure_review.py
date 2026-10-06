"""Independent structural graph and bounded publication checks."""

import argparse
import ast
import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from negative_fixtures import name_key
from phases import write
from Structure.sidecar import axiom_readings
from Structure.sources import file_digest


class StructureReviewTests(unittest.TestCase):
    def test_large_single_frontier_publication_preserves_elements(self):
        probe = pathlib.Path(__file__).with_name("structure_frontier_probe.py")
        results = [json.loads(subprocess.check_output([sys.executable, "-m", "tests.structure_frontier_probe", str(size)],
                                                     cwd=probe.parent.parent, text=True))
                   for size in [1, 128]]
        for result in results:
            self.assertEqual(result["reported_elements"], result["elements"])
            self.assertGreater(result["artifact_bytes"], result["frontier_bytes"])

    def test_publication_reads_large_rows_in_bounded_chunks(self):
        from Structure.sidecar import publish
        rows = [{"frontier": "x" * (3 * 64 * 1024)}, {"frontier": "last"}]
        encoded = b"\n".join(json.dumps(row).encode() for row in rows) + b"\n"
        test = self

        class BoundedReader(io.BytesIO):
            def read(self, size=-1):
                test.assertGreater(size, 0, "publication must not read the whole row")
                test.assertLessEqual(size, 64 * 1024, "publication read bound")
                return super().read(size)

            def __iter__(self):
                test.fail("publication must not buffer a whole JSONL row")

        with tempfile.TemporaryDirectory() as scratch:
            directory = pathlib.Path(scratch)
            source = directory / "rows.jsonl"
            original_open = pathlib.Path.open

            def open_file(path, *args, **kwargs):
                return BoundedReader(encoded) if path == source else original_open(path, *args, **kwargs)

            with patch.object(pathlib.Path, "open", open_file):
                publish(directory, {"schema": "census-structure"}, source)
            self.assertEqual(json.loads((directory / "census-structure.json").read_text()),
                             {"schema": "census-structure", "rows": rows})

    def graph(self, declarations):
        from Structure.graph import analyse
        from Structure.store import Store
        with tempfile.TemporaryDirectory() as scratch:
            folder = pathlib.Path(scratch)
            store = Store(folder / "store.sqlite")
            keys = [("Fixture", name_key(n), n) for n in declarations]
            try:
                store.module("Fixture", [], "repository")
                for name, value in declarations.items():
                    store.declaration("Fixture", name_key(name), "theorem",
                                      None if value is None else [name_key(n) for n in value])
                rows = folder / "rows.jsonl"
                summary = analyse(store, keys, rows, [], axioms={k[1:]: [] for k in keys})
                return {r["statement_id"]: r for r in map(json.loads, rows.read_text().splitlines())}, summary
            finally:
                store.close()

    def test_direct_depth_propagates_unreadable_prerequisite(self):
        rows, summary = self.graph({"a": None, "b": ["a"], "c": []})
        self.assertEqual(summary["direct_depths"], {"a": None, "b": None, "c": 0},
                         "directDepthFailurePropagation")
        self.assertEqual(rows["a"]["status"], "unavailable")
        self.assertIsNone(rows["b"]["readings"]["frozen_dag_depth"])

    def test_cycle_excluded_consumer_cannot_publish_complete_zero(self):
        rows, _ = self.graph({"a": ["a"], "x": ["a", "z"], "z": []})
        self.assertEqual((rows["z"]["status"], rows["z"]["readings"]["descendant_subgraph_size"]),
                         ("partial", None), "cycleExcludedConsumerDescendants")
        self.assertEqual(rows["z"]["missing_fields"], ["descendant_subgraph_size"])
        self.assertEqual(rows["a"]["reason"], "graph_cycle")
        self.assertIsNone(rows["x"]["readings"]["frozen_dag_depth"])



if __name__ == "__main__":
    unittest.main()
