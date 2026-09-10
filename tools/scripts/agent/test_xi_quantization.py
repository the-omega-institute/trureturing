"""Scientific behavior checks; no Torch, Arb, GPU, or network is needed."""

from fractions import Fraction as F
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import xi_quantization as q


def determinant(x, y):
    a = [[F(1), x, y], [x, F(1), x], [y, x, F(1)]]
    return sum(a[0][i] * a[1][(i+1) % 3] * a[2][(i+2) % 3]
               - a[0][i] * a[1][(i+2) % 3] * a[2][(i+1) % 3]
               for i in range(3))


class QuantizationTests(unittest.TestCase):
    def test_closed_endpoint_ambiguity_is_not_an_exact_tie(self):
        self.assertIsNone(q.certified_bin((49, 51, 100), 1))
        self.assertIsNone(q.certified_bin((49, 50, 100), 1))
        self.assertEqual(1, q.certified_bin((50, 51, 100), 1))

    def test_ties_round_toward_positive_infinity(self):
        for numerator, expected in [(-3, -1), (-1, 0), (1, 1), (3, 2)]:
            self.assertEqual(expected, q.certified_bin((numerator, numerator, 2), 1))

    def test_classification_matches_all_principal_minors(self):
        for m in range(1, 8):
            for kx in range(-m-1, m+2):
                for ky in range(-m-1, m+2):
                    x, y = F(kx, m), F(ky, m)
                    minors = [1-x*x, 1-y*y, determinant(x, y)]
                    expected = ("indefinite" if min(minors) < 0 else
                                "pd" if min(minors) > 0 else "singular")
                    self.assertEqual(expected, q.entrywise_class(m, kx, ky))

    def test_actual_200_witness_and_large_integer_products(self):
        record = q.entrywise_witness(200, 200, 199)
        self.assertEqual("-1/40000", record["determinant"])
        self.assertEqual("-1/100", record["normalized_quadratic_value"])
        self.assertEqual([1, -2, 1], record["normalized_vector"])
        for m in [200, 10**10]:
            record = q.entrywise_witness(m, m, m-1)
            self.assertEqual(str(-F(1, m*m)), record["determinant"])
            self.assertEqual(-2*m, record["quadratic_value"])

    def test_schur_reconstruction_including_singular_boundaries(self):
        for m in range(1, 6):
            for kx in range(-m, m+1):
                for kb in range(-m, m+1):
                    x, beta = F(kx, m), F(kb, m)
                    y = x*x+(1-x*x)*beta
                    det = determinant(x, y)
                    self.assertEqual((1-x*x)**2*(1-beta*beta), det)
                    self.assertEqual("pd" if det > 0 else "singular",
                                     q.schur_class(m, kx, kb))
                    q.schur_witness(m, kx, kb)
        y = F(1, 2)**2+(1-F(1, 2)**2)*F(1, 2)
        self.assertEqual(F(5, 8), y)

    def test_missing_resolution_prevents_complete_publication(self):
        coverage = q.Coverage(1, 4)
        coverage.record(1, True)
        coverage.record(2, False)
        coverage.record(3, True)
        self.assertEqual([[1, 1], [3, 3]], coverage.summary()["completed_intervals"])
        self.assertEqual([[2, 2], [4, 4]], coverage.summary()["unresolved_ranges"])
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "completed.md"
            report.write_text("existing completed evidence\n")
            with self.assertRaises(ValueError):
                q.publish_report(report, {"status": "incomplete", "coverage": coverage.summary()})
            self.assertEqual("existing completed evidence\n", report.read_text())
        coverage.record(4, True)
        self.assertEqual(1, coverage.summary()["unresolved_count"])

    def test_stream_serialization_is_explicit_and_ordered(self):
        payload = q.stream_row(200, 200, 199, -200, "indefinite", "singular")
        self.assertEqual(b"200,200,199,-200,indefinite,singular\n", payload)
        a = q.stream_row(1, 1, 1, -1, "singular", "singular")
        self.assertNotEqual(hashlib.sha256(a+payload).digest(),
                            hashlib.sha256(payload+a).digest())

    def test_range_guard_rejects_outside_scientific_domain_before_allocation(self):
        for first, last, chunk in [(0, 2, 1), (2, 1, 1), (1, 1400001, 1), (1, 2, 0)]:
            with self.assertRaises(ValueError):
                q.validate_range(first, last, chunk)

    def test_gpu_nonnegative_candidate_cannot_hide_exact_negative(self):
        summary = q.comparison_summary()
        q.compare_candidate(summary, 200, [200, 199, -200], "indefinite", "singular",
                            ([200, 200, -200], 1, 1, 0))
        self.assertEqual(1, summary["compared_count"])
        self.assertEqual(1, summary["entrywise_class_mismatches"])
        self.assertEqual(1, summary["bin_mismatches_by_coordinate"]["y"])
        self.assertEqual(1, summary["entrywise_confusion_exact_then_candidate"]["indefinite"]["singular"])
        self.assertEqual(200, summary["sign_examples"][0]["m"])

    def test_real_report_writer_separates_certification_from_publication(self):
        for failure in (None, "before_replace", "directory_sync", "failure_record_sync", "success_record_sync"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                report = root / "completed.md"
                report.write_text("existing completed evidence\n")
                args = SimpleNamespace(first=1, last=3, chunk=2, precision=256, digits=40,
                                       mode="cpu", state_dir=str(root / "state"), report=str(report))
                intervals = {"x": (0, 0, 1), "y": (0, 0, 1), "beta": (0, 0, 1)}
                receipt = {"coarse_intervals": {"gap": (1, 1, 1)}}
                environment = {"dependencies": {"torch": "2.8.0", "numpy": "2.0.2", "python-flint": "0.8.0"}}
                replace = q.state_store.os.replace
                sync_directory = q.state_store.sync_directory

                def replace_or_fail(source, destination):
                    if Path(destination) == report and failure == "before_replace":
                        raise OSError("injected report replacement failure")
                    replace(source, destination)

                def sync_or_fail(directory):
                    if Path(directory) == report.parent and failure in ("directory_sync", "failure_record_sync"):
                        raise OSError("injected report directory sync failure")
                    if Path(directory) == root / "state" and failure in ("failure_record_sync", "success_record_sync"):
                        visible = json.loads(next((root / "state").glob("run-*.json")).read_text())
                        if visible["status"] in ("publication_failed", "complete"):
                            raise OSError("injected runtime record directory sync failure")
                    sync_directory(directory)

                output = io.StringIO()
                with (patch.object(q, "generate_inputs", return_value=(intervals, receipt)),
                      patch.object(q, "system_evidence", return_value=environment),
                      patch.object(q.sys, "version_info", (3, 12)),
                      patch.dict(os.environ, {"GPU5040_SHARED_ROOT": str(root / "shared")}),
                      patch.object(q.state_store.os, "replace", side_effect=replace_or_fail),
                      patch.object(q.state_store, "sync_directory", side_effect=sync_or_fail),
                      redirect_stdout(output)):
                    self.assertEqual(1 if failure else 0, q.run(args))
                record = json.loads(next((root / "state").glob("run-*.json")).read_text())
                summary = json.loads(output.getvalue())
                self.assertEqual("complete" if failure in (None, "success_record_sync") else "publication_failed",
                                 record["status"])
                self.assertEqual("recording_failed" if failure == "success_record_sync" else record["status"],
                                 summary["status"])
                self.assertEqual("complete", record["mathematical_status"])
                self.assertEqual("complete", summary["mathematical_status"])
                self.assertEqual(3, record["coverage"]["classified_count"])
                self.assertEqual([], record["coverage"]["unresolved_ranges"])
                self.assertTrue(record["digest_complete_for_requested_interval"])
                expected_digest = hashlib.sha256(b"1,0,0,0,pd,pd\n2,0,0,0,pd,pd\n3,0,0,0,pd,pd\n").hexdigest()
                self.assertEqual(expected_digest, record["classification_sha256"])
                if failure not in (None, "success_record_sync"):
                    self.assertIn("injected report", record["error"])
                    self.assertEqual(record["error"], summary["error"])
                if failure in ("failure_record_sync", "success_record_sync"):
                    self.assertIn("injected runtime record", summary["runtime_record_error"])
                else:
                    self.assertIsNone(summary["runtime_record_error"])
                if failure == "before_replace":
                    self.assertEqual("existing completed evidence\n", report.read_text())
                else:
                    snapshot = json.loads(report.read_text().split("```json\n")[1].split("\n```")[0])
                    self.assertEqual(2, snapshot["schema_version"])
                    self.assertEqual("publication_unconfirmed", snapshot["status"])
                    self.assertEqual("complete", snapshot["mathematical_status"])
                    self.assertEqual(record["runtime_record"], snapshot["runtime_record"])
                    for key in ("coverage", "exact_counts", "classification_sha256"):
                        self.assertEqual(record[key], snapshot[key])
                    self.assertIn("before replacement", snapshot["publication_contract"])
                    self.assertIn("persistence is uncertain", snapshot["publication_contract"])

    def test_tail_rational_bound_and_strict_hypotheses(self):
        intervals = {"x": (999196806720852614, 999196806720852615, 10**18),
                     "y": (996790337371607624, 996790337371607625, 10**18),
                     "beta": (-998866411947906582, -998866411947906581, 10**18)}
        coarse = {"gap": (1820249309832, 1820249309833, 10**18)}
        tail = q.tail_certificate(intervals, coarse)
        # Independent rational values of the paper's 5/(2M) + 1/(2M^2) at M=1400000.
        error = F(7000001, 3920000000000)
        self.assertEqual(1400000, tail["from_m"])
        self.assertEqual(error, F(tail["error_at_M"]))
        self.assertEqual(F(211525460221, 6125000000000000000), F(tail["gap_minus_error"]))
        self.assertEqual(F(1820249309832, 10**18), F(tail["gap_lower_used"]))
        for deficit in (F(0), F(1, 10**18)):
            gap = error-deficit
            with self.subTest(gap=gap), self.assertRaisesRegex(ValueError, "tail bounds failed"):
                q.tail_certificate(intervals, {"gap": (gap.numerator, gap.numerator, gap.denominator)})
            for name, sign in (("x", -1), ("x", 1), ("y", 1), ("beta", -1), ("beta", 1)):
                endpoint = sign*(1-F(1, 2800000)+deficit)
                changed = {**intervals, name: (endpoint.numerator, endpoint.numerator, endpoint.denominator)}
                message = "Schur tail strictness failed" if name == "beta" else "tail bounds failed"
                with self.subTest(name=name, sign=sign, deficit=deficit), self.assertRaisesRegex(ValueError, message):
                    q.tail_certificate(changed, coarse)
        with self.assertRaisesRegex(ValueError, "independent endpoint PD check failed"):
            q.tail_certificate({**intervals, "x": (3, 3, 4), "y": (0, 0, 1)}, coarse)


if __name__ == "__main__":
    unittest.main(verbosity=2)
