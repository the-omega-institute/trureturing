"""Executed regressions for the three-seat structural review of PR #6717."""

import argparse
import ast
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

from negative_fixtures import name_key
from phases import write
from Structure.sidecar import axiom_readings
from Structure.sources import file_digest


class StructureReviewTests(unittest.TestCase):
    def test_large_single_frontier_publication_streams_bounded_reads(self):
        from Structure.writing import jsonl_elements
        from tests.structure_frontier_probe import probe

        def bounded_copy(source, out, separator=b","):
            # Observe the real writer's IO. Small reads are legitimate, but
            # collecting even bounded chunks before writing is not streaming.
            consumed = emitted = reads = 0

            class Source:
                def read(_, size=-1):
                    nonlocal consumed, reads
                    self.assertTrue(0 < size <= 64 * 1024, "boundedFrontierReadSize")
                    self.assertLessEqual(consumed - emitted, 1, "frontierReadAheadBeforeOutput")
                    block = source.read(size)
                    consumed += len(block)
                    reads += bool(block)
                    return block

            class Output:
                def write(_, block):
                    nonlocal emitted
                    written = out.write(block)
                    emitted += written
                    return written

            count = jsonl_elements(Source(), Output(), separator)
            copies.append((consumed, reads, count))
            return count

        for size in [1, 128]:
            copies = []
            with patch("Structure.graph.jsonl_elements", side_effect=bounded_copy), \
                 patch("Structure.sidecar.jsonl_elements", side_effect=bounded_copy), \
                 patch("resource.getrusage", side_effect=AssertionError("functionalFrontierMustNotMeasureRSS")):
                result = probe(size)
            self.assertEqual(result["reported_elements"], result["elements"])
            self.assertGreater(result["artifact_bytes"], result["frontier_bytes"])
            self.assertEqual(len(copies), 2, "frontierAndPublicationWriterExecuted")
            self.assertEqual(copies[0][0], result["frontier_bytes"])
            self.assertGreater(copies[1][0], result["frontier_bytes"])
            self.assertEqual([copy[2] for copy in copies], [result["elements"], 1])
            self.assertTrue(all(copy[1] > 1 for copy in copies), "multiBufferFrontierAndSingleRow")

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

    def test_regenerated_custom_report_supplies_sidecar_axioms(self):
        # Execute the production provenance branch and sidecar handoff. Other
        # census phases are deliberately outside this regression's input cone.
        import pipeline
        tree = ast.parse(pathlib.Path(pipeline.__file__).read_text())
        execute = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "execute")
        body = next(n for n in execute.body if isinstance(n, ast.Try)).body
        provenance = next(n for n in body if isinstance(n, ast.If) and n.orelse)
        handoff = next(n for n in body if isinstance(n, ast.If) and
                       isinstance(n.test, ast.UnaryOp) and
                       isinstance(n.test.operand, ast.Attribute) and n.test.operand.attr == "no_structure")
        program = compile(ast.Module(body=[provenance, handoff], type_ignores=[]), pipeline.__file__, "exec")
        with tempfile.TemporaryDirectory() as scratch:
            repository = pathlib.Path(scratch).resolve()
            directory = repository / "run"
            (directory / "logs").mkdir(parents=True)
            source = repository / "A.lean"
            source.write_text("theorem a : True := True.intro\n")
            key = ("A", name_key("a"), "id-a")
            true_axioms = ["Classical.choice", "Quot.sound", "propext"]
            module = {"module": "A", "source_path": "A.lean", "source_sha256": file_digest(source),
                      "declarations": [{"kind": "theorem", "name_key": key[1],
                                        "statement_id": key[2], "axioms": []}]}
            stale = repository / "custom-stale.json"
            write(stale, {"modules": [module]})
            regenerated = repository / ".lake/build/stratalint/raw-lean-report.json"
            state, verified, exported = {}, [], []

            def step(command, label, **_):
                if "verify" in command:
                    report = pathlib.Path(command[command.index("--report") + 1])
                    if report == stale:
                        raise RuntimeError("stale transitive axiom closure")
                    self.assertEqual(axiom_readings(repository, report, [key]), {key[1:]: true_axioms})
                    verified.append(report)
                elif command == ["make", "lean-report"]:
                    regenerated.parent.mkdir(parents=True)
                    module["declarations"][0]["axioms"] = true_axioms
                    write(regenerated, {"modules": [module]})
                elif command[:2] == ["make", "truth-export"]:
                    report = pathlib.Path(next(c.removeprefix("LEAN_REPORT=") for c in command
                                              if c.startswith("LEAN_REPORT=")))
                    self.assertIn(report, verified)
                    exported.append(report)
                    (directory / "logs/truth_export.log").write_text("TRUTH_EXPORT out=" + str(report) + "\n")

            def sidecar(repo, _directory, report):
                return {"report": str(report), "axioms": axiom_readings(repo, report, [key])}

            scope = dict(pipeline.__dict__, repository=repository, directory=directory, state=state,
                         env={}, step=step, options=argparse.Namespace(fixture_truth_export=None,
                         lean_report=str(stale), no_structure=False))
            with patch("Structure.sidecar.run_sidecar", side_effect=sidecar):
                exec(program, scope)
            self.assertEqual(state["structure"], {"report": str(exported[0]),
                             "axioms": {key[1:]: true_axioms}}, "verifiedReportAxiomJoin")
            self.assertTrue(state["report_provenance"]["regenerated"])
            self.assertEqual(axiom_readings(repository, stale, [key]), {key[1:]: []})


if __name__ == "__main__":
    unittest.main()
