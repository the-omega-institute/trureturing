"""Executable input and emission contracts for the run-local census producer."""

import importlib.util
import pathlib
import tempfile
import unittest
from unittest import mock
import argparse
import json
import os
import subprocess
import sys

PROGRAM = pathlib.Path(__file__).resolve().parents[1] / "pipeline.py"


def statement_id(value):
    return "sha256:" + format(value, "064x")


class PipelineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("census_pipeline", PROGRAM)
        cls.program = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.program)

    def test_completion_cannot_be_supplied(self):
        for field in ("queryCompleted", "query_completed", "completed", "candidates"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.program.parse_request({"root": "Root", "report": "report.json", field: True})

    def test_duplicate_names_in_different_modules_keep_distinct_keys(self):
        nodes = [{"repo_path": f"D5/{module}.lean", "freeze_status": "frozen",
                  "declarations": [{"kind": "theorem", "declaration_name_key": "ns(n0,4:same)",
                                    "statement_id": identity}]}
                 for module, identity in (("A", statement_id(1)), ("B", statement_id(2)))]
        self.assertEqual(self.program.frozen_keys({"nodes": nodes}), [
            ("D5.A", "ns(n0,4:same)", statement_id(1)),
            ("D5.B", "ns(n0,4:same)", statement_id(2))])

    def test_repeated_statement_id_is_rejected(self):
        node = {"repo_path": "D5/A.lean", "freeze_status": "frozen", "declarations": [
            {"kind": "theorem", "declaration_name_key": "ns(n0,4:same)", "statement_id": statement_id(0)}]}
        with self.assertRaises(ValueError):
            self.program.frozen_keys({"nodes": [node, node]})

    def test_export_path_is_read_from_the_canonical_writer_receipt(self):
        log = "build output\nTRUTH_EXPORT nodes=4 source_commit=head out=/tmp/with spaces/current.json\n"
        self.assertEqual(self.program.exported_path(log), pathlib.Path("/tmp/with spaces/current.json").resolve())
        for bad in ("", log + log, "TRUTH_EXPORT nodes=4 source_commit=head\n"):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.program.exported_path(bad)

    def test_partial_certification_never_uses_subset_denominator(self):
        summary = {"requested_keys": 4, "status": "partial",
                   "counts": {"accounted": 1, "certified": 1, "observed": 0},
                   "certified_complete": True}
        with self.assertRaisesRegex(ValueError, "certified_complete"):
            self.program.validate_summary(summary, requested=4, accounted=1)
        summary["certified_complete"] = False
        self.program.validate_summary(summary, requested=4, accounted=1)
        summary["requested_keys"] = 1
        with self.assertRaisesRegex(ValueError, "requested"):
            self.program.validate_summary(summary, requested=4, accounted=1)

    def test_fixture_export_rejects_stale_report_before_queries(self):
        with tempfile.TemporaryDirectory() as directory:
            report = pathlib.Path(directory) / "stale.json"
            report.write_text(json.dumps({"source_commit": "0" * 40, "nodes": []}))
            options = argparse.Namespace(output=str(pathlib.Path(directory) / "run"),
                                         fixture_truth_export=str(report))
            with mock.patch("resources.run", side_effect=AssertionError("query started")):
                with self.assertRaisesRegex(ValueError, "synthetic fixture"):
                    self.program.execute(options)

    def test_fixture_export_rejects_production_module_paths(self):
        for path in ("D5/S0/Production.lean", "LeanInformationAudit/Tests/../../D5/Bad.lean"):
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "fixture module"):
                self.program.validate_fixture_export({"source_commit": "fixture-head",
                                                      "nodes": [{"repo_path": path}]})

    def test_report_provenance_regenerates_before_truth_export(self):
        self._report_provenance([False, True], True, True)

    def test_report_provenance_rejects_failed_regeneration(self):
        self._report_provenance([False, False], True, False)

    def test_report_provenance_accepts_fresh_without_regeneration(self):
        self._report_provenance([True], False, True)

    def _report_provenance(self, verifications, regenerate, exported):
        class ExportReached(Exception):
            pass
        calls = []
        pending = list(verifications)
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary) / "run"
            options = argparse.Namespace(output=str(directory), fixture_truth_export=None,
                                         lean_report="donor-report.json")
            def step(command, logs, label, **kwargs):
                logs.mkdir(parents=True, exist_ok=True)
                (logs / (label + ".log")).write_text("")
                calls.append(command)
                if "verify" in command:
                    self.assertIn("lean-report-input.sh", command[1])
                    if not pending.pop(0):
                        raise RuntimeError("raw Lean report producer is stale for current repository inputs")
                if command[:2] == ["make", "truth-export"]:
                    self.assertFalse(pending, "reportProvenanceBeforeTruthExport")
                    self.assertEqual(["make", "lean-report"] in calls, regenerate,
                                     "reportProvenanceBeforeTruthExport")
                    if regenerate:
                        self.assertTrue(any(arg.endswith("/.lake/build/stratalint/raw-lean-report.json")
                                            for arg in command), "reportProvenanceBeforeTruthExport")
                    raise ExportReached()
                return {"wall_seconds": 0, "rss_budget_gib": None}
            env = json.dumps(dict(os.environ)).encode()
            with mock.patch("resources.run", side_effect=step), mock.patch.object(
                    self.program.subprocess, "check_output", return_value=env):
                if exported:
                    with self.assertRaises(ExportReached):
                        self.program.execute(options)
                else:
                    with self.assertRaisesRegex(RuntimeError, "producer is stale"):
                        self.program.execute(options)
            self.assertFalse(pending, "reportProvenanceBeforeTruthExport")
            self.assertEqual(any(c[:2] == ["make", "truth-export"] for c in calls), exported)

    def test_manifest_excludes_scope_payloads(self):
        from Certificate import emission
        first = ["str", ["anonymous"], "First"]
        second = ["str", ["anonymous"], "Second"]
        rows = [{"theorem_name": first, "statement_id": "sha256:" + format(1, "064x"),
                 "payload": {"import_scope": [first, second] * 1000}}]
        keys = [("Fixture", "ns(n0,5:First)", rows[0]["statement_id"])]
        source = emission.manifest_source(rows, keys, "head", "digest", "Root")
        self.assertNotIn("Second", source)
        self.assertNotIn("import_scope", source)
        self.assertNotIn("CensusRun.Scopes", source)

    def test_budget_acceptance_reading_is_not_a_byte_level_stop(self):
        from resources import check_budget, ResourceRejected
        with self.assertRaisesRegex(ResourceRejected, "free memory"):
            check_budget(29, 0, 4 * 1024 ** 3)
        check_budget(83, 4 * 1024 ** 3 + 2965504, 4 * 1024 ** 3)
        with self.assertRaisesRegex(ResourceRejected, "rss"):
            check_budget(83, 8 * 1024 ** 3 + 1, 4 * 1024 ** 3)

    def test_incomplete_rows_never_claim_complete_certification(self):
        summary = {"requested_keys": 1, "status": "complete", "certified_complete": False,
                   "counts": {"accounted": 1, "certified": 0, "observed": 0,
                              "observed_query_incomplete": 1}}
        self.program.validate_summary(summary, requested=1, accounted=1)
        summary["certified_complete"] = True
        with self.assertRaisesRegex(ValueError, "certified_complete"):
            self.program.validate_summary(summary, requested=1, accounted=1)

    def test_publication_diagnostic_uses_the_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = pathlib.Path(temporary) / "publication.json"
            self.assertEqual(self.program.publication_result(None), {"status": "not_requested"})
            value = {"certificate": {"name": "CensusRun.accountingCertificate", "axioms": ["propext"]},
                     "query_receipt_digest": "sha256:" + "c" * 64}
            path.write_text(json.dumps(value))
            result = self.program.publication_result(path)
            self.assertEqual(result["status"], "published")
            self.assertEqual(result["certificate"], value["certificate"])
            self.assertEqual(result["query_receipt_digest"], value["query_receipt_digest"])


if __name__ == "__main__":
    unittest.main()
