"""Review regressions: exercise the emitter entrypoint and outer measurement."""

import copy
import hashlib
import inspect
import json
import pathlib
import re
import tempfile
import unittest
from unittest.mock import patch

import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from Certificate import certificate_benchmark
from Certificate import emission
from Certificate import manifest
from Certificate import handoff
from tests.test_buckets import authorities


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode() + b"\n"


def digest(value):
    return "sha256:" + hashlib.sha256(canonical(value)).hexdigest()


def fixture(directory, rows=None, report_ids=None):
    rows = rows if rows is not None else authorities([0, 1])[0]
    report_ids = report_ids if report_ids is not None else [r["statement_id"] for r in rows]
    report = {"source_commit": "fixture-head", "nodes": [{"repo_path": "Fixture.lean",
        "freeze_status": "frozen", "declarations": [{"kind": "theorem", "statement_id": wire,
        "declaration_name_key": f"ns(n0,2:T{i})"} for i, wire in enumerate(report_ids)]}]}
    report_path = directory / "report.json"
    report_path.write_bytes(canonical(report))
    report_sha = "sha256:" + hashlib.sha256(report_path.read_bytes()).hexdigest()
    j2 = [dict(row, **{"class": "observed", "payload": {"root": ["str", ["anonymous"], "Fixture"],
        "query_completed": True, "import_scope": {"modules": [], "completed": True}}}) for row in rows]
    compact = copy.deepcopy(j2)
    for row in compact:
        row["payload"]["import_scope"] = None
    rows_sha = "sha256:" + hashlib.sha256(b"".join(canonical(r) for r in compact)).hexdigest()
    programs = [["tools/lean-inspector/Census/" + name, "sha256:" + "0" * 64]
                for name in ["phases.py", "emission_cache.py", "streaming.py"]]
    emitter = digest([(path.rsplit("/", 1)[1], sha[7:]) for path, sha in programs])
    inputs = {"head": "fixture-head", "export_sha256": report_sha, "module_names": [],
        "scopes": [["Fixture", []]], "programs": programs,
        "rows": {"artifact": "rows.jsonl", "sha256": rows_sha},
        "expanded_rows_cache_key": digest([rows_sha, [], [["Fixture", []]], emitter])}
    receipt = {"inputs": inputs, "digest": digest(inputs), "rows_sha256": rows_sha}
    census = dict(head_sha="fixture-head", report_sha256=report_sha,
        schema="lean-information-disposition-census", query_verification="lean_streaming_query", rows=j2)
    census_path, receipt_path = directory / "census.json", directory / "receipt.json"
    census_path.write_bytes(canonical(census))
    rows_path = directory / "rows.jsonl"
    rows_path.write_bytes(b"".join(canonical(row) for row in compact))
    receipt_path.write_bytes(canonical(receipt))
    return report_path, rows_path, receipt_path, rows


class ReviewFixTests(unittest.TestCase):
    def test_whole_stream_publication_entrypoint(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = pathlib.Path(temp)
            report, census, receipt, _ = fixture(directory)
            try:
                if len(inspect.signature(manifest.emit).parameters) == 4:
                    # Run the original production generator successfully in the red control.
                    response = directory / "partition.json"
                    response.write_text(json.dumps({"entries": json.loads(census.read_bytes())["rows"]}))
                    paths = directory / "paths.json"
                    paths.write_text(json.dumps([str(response)]))
                    manifest.emit(directory / "out", report, paths, "Fixture")
                else:
                    manifest.emit(directory / "out", report, census, receipt, "Fixture")
            except (TypeError, ValueError, KeyError) as error:
                self.fail("wholeStreamPublicationHandoff: " + str(error))
            driver = (directory / "out/CensusPublish/Root.lean").read_text()
            self.assertIn(str(census), driver, "wholeStreamPublicationHandoff")
            self.assertIn(str(receipt), driver, "wholeStreamPublicationHandoff")
            self.assertNotIn(" receipts ", driver, "wholeStreamPublicationHandoff")
            original = census.read_bytes()
            edited = [json.loads(line) for line in original.splitlines()]
            edited[0]["payload"]["query_completed"] = False
            census.write_bytes(b"".join(canonical(row) for row in edited))
            with self.assertRaisesRegex(ValueError, "whole_stream_rows_binding",
                                        msg="wholeStreamRowsBinding"):
                manifest.emit(directory / "edited", report, census, receipt, "Fixture")
            census.write_bytes(original)
            edited = json.loads(receipt.read_bytes())
            edited["digest"] = "sha256:" + "f" * 64
            receipt.write_bytes(canonical(edited))
            with self.assertRaisesRegex(ValueError, "whole_stream_receipt_digest",
                                        msg="wholeStreamReceiptDigest"):
                manifest.emit(directory / "receipt-edit", report, census, receipt, "Fixture")

    def test_publication_reads_compact_rows(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = pathlib.Path(temp)
            report, rows, receipt, _ = fixture(directory)
            opens = []
            original_open = pathlib.Path.open

            def guarded_open(path, *args, **kwargs):
                self.assertNotEqual(path.name, "census.json", "publicationReadsCompactRows")
                if path == rows:
                    opens.append(path)
                return original_open(path, *args, **kwargs)

            with patch.object(pathlib.Path, "open", guarded_open):
                manifest.emit(directory / "out", report, rows, receipt, "Fixture")
                handoff.publish(directory / "publication.json", {"certificate": {"name": "Fixture"}})
            self.assertEqual(opens, [rows], "publicationReadsCompactRows")
            driver = (directory / "out/CensusPublish/Root.lean").read_text()
            self.assertNotIn("census.json", driver, "publicationReadsCompactRows")

    def test_compact_rows_linear_decoding(self):
        work = []
        for size in [65536, 131072, 262144]:
            with tempfile.TemporaryDirectory() as temp:
                directory = pathlib.Path(temp)
                rows, _ = authorities([1])
                rows[0]["theorem_name"] = ["str", ["anonymous"], "T" * size]
                report, compact, receipt, _ = fixture(directory, rows)
                decoded = []
                original_decode = json.JSONDecoder.raw_decode

                def count_decode(decoder, text, idx=0):
                    decoded.append(len(text))
                    return original_decode(decoder, text, idx)

                with patch.object(json.JSONDecoder, "raw_decode", count_decode):
                    result, _ = handoff.read(compact, receipt,
                        "sha256:" + hashlib.sha256(report.read_bytes()).hexdigest(), "fixture-head")
                self.assertEqual(result[0]["theorem_name"], rows[0]["theorem_name"])
                self.assertEqual(len(decoded), 2, "compactRowsLinearDecoding")
                self.assertEqual(sum(decoded), len(compact.read_bytes()) + len(receipt.read_bytes()),
                                 "compactRowsLinearDecoding")
                work.append(sum(decoded))
        self.assertLessEqual(work[1], 2 * work[0], "compactRowsLinearDecoding")
        self.assertLessEqual(work[2], 2 * work[1], "compactRowsLinearDecoding")

    def test_pipeline_prepares_without_reading_rows(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = pathlib.Path(temp)
            report, rows, receipt, _ = fixture(directory)
            original_open = pathlib.Path.open

            def guarded_open(path, *args, **kwargs):
                self.assertNotIn(path.name, ["rows.jsonl", "census.json"], "publicationReadsCompactRows")
                return original_open(path, *args, **kwargs)

            with patch.object(pathlib.Path, "open", guarded_open):
                manifest.prepare(directory / "out", report, rows, receipt, "Fixture")
            self.assertIn(" generate ", (directory / "out/CensusPublish/Root.lean").read_text())

    def test_inventory_duplicate_before_malformed_report_entrypoint(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = pathlib.Path(temp)
            rows = authorities([1, 1])[0]
            report, census, receipt, _ = fixture(directory, rows, ["sha256:" + "0" * 63])
            # Historical invocation is confined to this regression's red control.
            if len(inspect.signature(manifest.emit).parameters) == 4:
                response = directory / "partition.json"
                response.write_text(json.dumps({"entries": rows}))
                paths = directory / "paths.json"
                paths.write_text(json.dumps([str(response)]))
                args = (directory / "out", report, paths, "Fixture")
            else:
                args = (directory / "out", report, census, receipt, "Fixture")
            with self.assertRaisesRegex(ValueError, "IE-C035", msg="inventoryDuplicateBeforeEmitterCodec"):
                manifest.emit(*args)

    def test_whole_path_budget_uses_outer_measurement(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = pathlib.Path(temp)
            report = directory / "report.json"
            report.write_text('{"source_commit":"fixture-head"}')
            (directory / "CensusRun").mkdir()
            build = {"wall_s": 1, "max_process_peak_rss_bytes": 100}
            (directory / "CensusRun/Root.checked.build.json").write_text(json.dumps(build))
            outer = {"wall_seconds": 400, "peak_rss_bytes": 3 * 1024 ** 3}
            with patch.object(certificate_benchmark, "run", return_value=outer):
                result = certificate_benchmark.benchmark(directory, report, directory)
            self.assertFalse(result["whole_path_target_met"], "wholePathIncludesValidationDriver")
            self.assertTrue(result["profile_required"], "wholePathIncludesValidationDriver")

    def test_adaptive_leaf_bound(self):
        rows, keys = authorities(range(1000))
        sources = emission.bucket_sources(rows, keys, b=0)
        sizes = [int(n) for source in sources.values() if ".chunk0 : Nat" in source
                 for n in re.findall(r"\.n : Nat := (\d+)", source)]
        self.assertTrue(sizes, "adaptiveLeafBound")
        self.assertLessEqual(max(sizes), 128, "adaptiveLeafBound")
        for source in sources.values():
            imports = re.findall(r"^public import (.*)$", source, re.M)
            if imports == ["LeanInformationAudit.Census.Certificate"]:
                continue
            self.assertEqual(len(imports), 2, "adaptiveTwoChildComposition")
            self.assertNotIn("decodeIds", source, "adaptiveNodeHasNoPackedIds")
            self.assertEqual(source.count("range_join"), 1, "adaptiveGenericJoin")


if __name__ == "__main__":
    unittest.main()
