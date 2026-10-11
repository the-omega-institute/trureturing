#!/usr/bin/env python3
"""Execution contract for the finite SPEC 9 consumer; fixtures are synthetic."""
import json
import subprocess
import sys
import time
import unittest
from fractions import Fraction
from pathlib import Path

BINARY = None
FIELDS = {"arena", "source_contract", "atom_readout", "seam_readout",
          "pyramid_coordinates", "association_coordinate", "continuation_target",
          "kernel", "escape_pairs", "escape_rate", "unique_capture",
          "layered_spectrum", "residuals", "disposition"}


def law(masses, **extra):
    return {"source_contract": {"kind": "declared-finite-law", "source": "synthetic",
            "window_length": 1, "native_contract": "initialized-high-to-low-high-suffix"},
            "law": masses, **extra}


def q(value):
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def source_validation_requests():
    invalid = [law(masses) for masses in (
        ["-1", "1", "1", "0", "0"], ["1", "0", "0", "0"],
        ["1/0", "0", "0", "0", "0"], ["0.5", "0", "0", "0", "0"],
        ["2", "0", "0", "0", "0"], ["0"] * 5)]
    for key, value in (("native_contract", "low-to-high"), ("window_length", 2),
                       ("physical_law_certified", True)):
        request = law(["1", "0", "0", "0", "0"])
        request["source_contract"][key] = value
        invalid.append(request)
    return invalid + [law(["1", "0", "0", "0", "0"], target=[1, 2, 3, 4, 5]),
                      law(["1", "0", "0", "0", "0"], archive=[[0, 0, 0]])]


EMPIRICAL = {"kind": "empirical-archive", "source": "synthetic-archive",
             "window_length": 1, "native_contract": "initialized-high-to-low-high-suffix"}
ARCHIVE = [[0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1]]
BAD_ARCHIVES = ([[1, 0, 1]], [[0, 1, 1]], [[2, 0, 0]], [[0, 0]], [[False, 0, 0]])
EXTREMA = (["1/2", "0", "0", "1/2", "0"], ["0", "1/2", "1/2", "0", "0"],
           ["0", "0", "0", "0", "1"], ["1", "0", "0", "0", "0"],
           ["0", "0", "1", "0", "0"])
GRID = [[a, b, c, e, 4-a-b-c-e] for a in range(5)
        for b in range(5-a) for c in range(5-a-b) for e in range(5-a-b-c)]
UNKNOWN = ({}, {"source_contract": {"kind": "unknown", "source": "unknown",
           "window_length": 1, "native_contract": "initialized-high-to-low-high-suffix"}})
LARGE_DENOMINATOR = 10 ** 40 + 39


class FiniteAnalysisContract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        """Execute all fixtures in two batches; retain each actual returned row."""
        accepted = [law(["1/5"] * 5)] + [law(masses) for masses in EXTREMA]
        accepted += [law(["1/5"] * 5, initial_readouts=["seam"],
                         layers=["guard", "reply", "atom"]),
                     {"source_contract": EMPIRICAL, "archive": ARCHIVE},
                     {"source_contract": EMPIRICAL, "archive": []}, *UNKNOWN,
                     {"arena": "unbounded"},
                     law([f"{LARGE_DENOMINATOR-1}/{LARGE_DENOMINATOR}",
                          f"1/{LARGE_DENOMINATOR}", "0", "0", "0"])]
        accepted += [law([f"{x}/4" for x in masses]) for masses in GRID]
        rejected = source_validation_requests() + [
            law(["1/5"] * 5, layers=["seam", "guard"]),
            law(["1/5"] * 5, initial_readouts=["delta"]),
            {"law": ["1", "0", "0", "0", "0"]}]
        rejected += [{"source_contract": EMPIRICAL, "archive": bad} for bad in BAD_ARCHIVES]
        cls.actual = {}
        for requests, code in ((accepted, 0), (rejected, 2)):
            started = time.monotonic()
            result = subprocess.run([str(BINARY), "--batch"], input=json.dumps(requests),
                                    text=True, capture_output=True, check=False)
            if result.returncode != code:
                raise AssertionError(f"[FAIL] BatchExit{code}: {result.stderr}{result.stdout}")
            reports = json.loads(result.stdout)
            if len(reports) != len(requests):
                raise AssertionError("[FAIL] BatchTotalOutput")
            for request, report in zip(requests, reports):
                cls.actual[json.dumps(request, sort_keys=True)] = (report, code)
            print(f"[PASS] BatchExit{code} requests={len(requests)} "
                  f"elapsed_seconds={time.monotonic()-started:.3f}", flush=True)

    def execute(self, request, code=0, direct=False):
        self.assertIsNotNone(BINARY, "executable path required")
        self.assertTrue(BINARY.is_file(), "[FAIL] ExecutableConsumerAbsent")
        if direct:
            result = subprocess.run([str(BINARY)], input=json.dumps(request), text=True,
                                    capture_output=True, check=False)
            self.assertEqual(result.returncode, code, result.stderr + result.stdout)
            report = json.loads(result.stdout)
        else:
            report, actual_code = self.actual[json.dumps(request, sort_keys=True)]
            self.assertEqual(actual_code, code)
        self.assertTrue(FIELDS <= report.keys(), report.keys())
        return report

    def batch(self, requests, code=0):
        self.assertTrue(BINARY.is_file(), "[FAIL] ExecutableConsumerAbsent")
        return [self.execute(request, code) for request in requests]

    def invalid(self, request):
        report = self.execute(request, 2)
        self.assertEqual(report["disposition"]["status"], "refuted")
        self.assertIsNone(report["escape_rate"])
        return report

    def test_source_validation(self):
        invalid = source_validation_requests()
        for report in self.batch(invalid, 2):
            self.assertEqual(report["disposition"]["status"], "refuted")
            self.assertIsNone(report["escape_rate"])
        self.execute(invalid[0], 2, direct=True)

    def test_actual_native_total_results(self):
        r = self.execute(law(["1/5"] * 5), direct=True)
        rows = r["atom_readout"]["states"]
        self.assertEqual([x["mode"] for x in rows], ["null", "2", "5", "25", "3"])
        self.assertEqual([x["bits_x2_y5_z3"] for x in rows], ARCHIVE)
        self.assertEqual([x["first_reply"] for x in rows], ["0", "2", "5", "7", "3"])
        self.assertEqual([x["suffix_reply"] for x in rows], ["5", None, "26", None, "18"])
        self.assertEqual([x["guard_accepts"] for x in rows], [True, False, True, False, True])
        self.assertEqual([x["parity_event"] for x in rows], [False, False, True, True, True])
        response = r["continuation_target"]["conditional_reply_law"]
        self.assertEqual({x["reply"]: q(x["mass"]) for x in response},
                         {None: Fraction(1, 3), "18": Fraction(1, 3), "26": Fraction(1, 3)})
        self.assertEqual(q(r["continuation_target"]["unconditional_rejection_mass"]), Fraction(2, 5))
        self.assertFalse(r["disposition"]["is_lean_proof"])
        self.assertFalse(r["source_contract"]["physical_law_certified"])

    def test_equal_coarse_different_association_and_response(self):
        a, b = self.batch([law(["1/2", "0", "0", "1/2", "0"]),
                           law(["0", "1/2", "1/2", "0", "0"])])
        self.assertEqual(a["pyramid_coordinates"], b["pyramid_coordinates"])
        self.assertEqual(q(a["association_coordinate"]["delta"]), Fraction(1, 4))
        self.assertEqual(q(b["association_coordinate"]["delta"]), Fraction(-1, 4))
        self.assertEqual(q(a["residuals"]["R_guard"]["value"]), Fraction(1, 2))
        self.assertEqual(q(b["residuals"]["R_guard"]["value"]), Fraction(-1, 2))
        self.assertNotEqual(a["continuation_target"]["conditional_reply_law"],
                            b["continuation_target"]["conditional_reply_law"])

    def test_extrema_reconstruction_and_apex(self):
        cases = EXTREMA
        reports = self.batch([law(masses) for masses in cases])
        for masses, r in zip(cases, reports):
            a, residual = r["association_coordinate"], r["residuals"]
            self.assertEqual([q(x) for x in a["reconstructed_law"]], [Fraction(x) for x in masses])
            self.assertEqual(q(residual["fiber_width"]), q(a["kappa_max"]) - q(a["kappa_min"]))
            self.assertEqual(q(residual["target_range_width"]), q(residual["fiber_width"]))
            self.assertEqual(q(residual["target_max"]) - q(residual["target_min"]),
                             q(residual["target_range_width"]))
            self.assertEqual(q(a["delta"]), q(a["determinant_from_cells"]))
            self.assertLessEqual(q(a["delta_min"]), q(a["delta"]))
            self.assertLessEqual(q(a["delta"]), q(a["delta_max"]))
        apex = reports[2]
        self.assertEqual(apex["residuals"]["R_guard"]["status"], "apex")
        self.assertEqual(q(apex["residuals"]["R_guard"]["value"]), 0)
        self.assertIsNone(apex["association_coordinate"]["conditional_endpoint_independent"])
        zero_event = reports[3]
        self.assertEqual(zero_event["residuals"]["R_guard"]["status"], "zero-conditioning-mass")
        self.assertIsNone(zero_event["residuals"]["R_guard"]["value"])
        self.assertIsNone(zero_event["continuation_target"]["conditional_reply_law"])

    def test_finite_count_kernel_capture_and_layer_identities(self):
        r = self.execute(law(["1/5"] * 5))
        self.assertEqual(r["arena"]["cardinality"], 5)
        self.assertEqual(r["arena"]["ordered_pair_denominator"], 20)
        self.assertEqual(r["escape_pairs"], [])
        self.assertEqual(r["escape_rate"], {"numerator": 0, "denominator": 20})
        unique = r["unique_capture"]
        self.assertEqual([x["count"] for x in unique], [2, 0, 0, 0])
        for row in unique:
            self.assertEqual(len(row["pairs"]), row["count"])
            self.assertEqual(q(row["leave_one_out_rate"]) - q(r["escape_rate"]), q(row["rate"]))
        k = r["kernel"]
        self.assertEqual(len(k["generated_nodes"]), 4)
        self.assertEqual(k["full_relation"], [[i == j for j in range(5)] for i in range(5)])
        self.assertEqual(len(k["subsets"]), 16)
        states = r["atom_readout"]["states"]
        values = [{"atom": state["mode"], "seam": state["seam"],
                   "guard": state["guard_accepts"], "reply": state["suffix_reply"]}
                  for state in states]
        for row in k["subsets"]:
            table = k["generated_nodes"][row["node"]]["relation"]
            expected = [[all(values[i][name] == values[j][name] for name in row["readouts"])
                         for j in range(5)] for i in range(5)]
            self.assertEqual(table, expected)
            count = sum(table[i][j] for i in range(5) for j in range(5) if i != j)
            self.assertEqual(row["escape_count"], count)
        tables = [node["relation"] for node in k["generated_nodes"]]
        self.assertEqual(len({json.dumps(table) for table in tables}), len(tables))
        def includes(coarse, fine):
            return all(not fine[i][j] or coarse[i][j] for i in range(5) for j in range(5))
        for edge in k["strict_edges"]:
            coarse, fine = tables[edge["from"]], tables[edge["to"]]
            self.assertTrue(includes(coarse, fine))
            self.assertNotEqual(coarse, fine)
            self.assertEqual(edge["capture_count"],
                             sum(coarse[i][j] and not fine[i][j]
                                 for i in range(5) for j in range(5) if i != j))
            middle = [table for table in tables if table != coarse and table != fine
                      and includes(coarse, table) and includes(table, fine)]
            self.assertEqual(edge["is_cover"], not middle)
        spectrum = r["layered_spectrum"]
        self.assertEqual([x["count"] for x in spectrum["layers"]], [0, 12, 0, 6, 2])
        self.assertTrue(spectrum["layers"][2]["collapsed"])
        self.assertEqual(spectrum["unresolved"]["count"], 0)
        self.assertEqual(sum(x["count"] for x in spectrum["layers"]) + spectrum["unresolved"]["count"], 20)
        self.assertEqual(sum(q(x["rate"]) for x in spectrum["layers"]) + q(spectrum["unresolved"]["rate"]), 1)
        pairs = [tuple(p) for x in spectrum["layers"] for p in x["pairs"]]
        self.assertEqual(len(pairs), len(set(pairs)))
        self.assertEqual(len(spectrum["first_capture"]), 20)
        for address in spectrum["first_capture"]:
            self.assertIn(address["pair"], spectrum["layers"][address["first_layer"]]["pairs"])
        initial = self.execute(law(["1/5"] * 5, initial_readouts=["seam"],
                                  layers=["guard", "reply", "atom"]))
        self.assertEqual([x["count"] for x in initial["layered_spectrum"]["layers"]], [12, 0, 6, 2])
        self.invalid(law(["1/5"] * 5, layers=["seam", "guard"]))
        self.invalid(law(["1/5"] * 5, initial_readouts=["delta"]))

    def test_empirical_legal_pushforward_and_empty_archive(self):
        contract = EMPIRICAL
        r = self.execute({"source_contract": contract,
                          "archive": ARCHIVE})
        self.assertEqual(r["source_contract"]["sample_count"], 5)
        self.assertEqual([q(x) for x in r["source_contract"]["pushforward_law"]], [Fraction(1, 5)] * 5)
        self.assertEqual(r["association_coordinate"]["acquisition"], "empirical-archive-pushforward")
        self.assertFalse(r["source_contract"]["iid_assumed"])
        bad_archives = BAD_ARCHIVES
        for report in self.batch([{"source_contract": contract, "archive": bad}
                                  for bad in bad_archives], 2):
            self.assertEqual(report["disposition"]["status"], "refuted")
        empty = self.execute({"source_contract": contract, "archive": []})
        self.assertIsNone(empty["association_coordinate"])
        self.assertEqual(empty["disposition"]["status"], "open")
        self.assertEqual(empty["arena"]["cardinality"], 5)

    def test_unknown_missing_and_unbounded_contracts(self):
        for request in UNKNOWN:
            r = self.execute(request)
            self.assertEqual(r["disposition"]["status"], "open")
            self.assertIsNone(r["pyramid_coordinates"])
            self.assertIsNone(r["residuals"])
            self.assertFalse(r["disposition"]["is_lean_proof"])
            self.assertEqual(r["arena"]["ordered_pair_denominator"], 20)
        self.invalid({"law": ["1", "0", "0", "0", "0"]})
        r = self.execute({"arena": "unbounded"})
        self.assertEqual(r["disposition"]["status"], "deferred")
        self.assertIsNone(r["escape_rate"])
        self.assertIsNone(r["arena"]["ordered_pair_denominator"])

    def test_exact_large_denominator_and_finite_law_grid(self):
        d = LARGE_DENOMINATOR
        r = self.execute(law([f"{d-1}/{d}", f"1/{d}", "0", "0", "0"]))
        self.assertEqual(q(r["pyramid_coordinates"]["X"]), Fraction(1, d))
        cases = GRID
        reports = self.batch([law([f"{x}/4" for x in masses]) for masses in cases])
        for masses, r in zip(cases, reports):
            p = [Fraction(x, 4) for x in masses]
            delta = p[0]*p[3] - p[1]*p[2]
            x, y, z = p[1]+p[3], p[2]+p[3], p[4]
            bottom = 1-z
            coordinates = r["pyramid_coordinates"]
            self.assertEqual([q(coordinates[name]) for name in ("X", "Y", "Z", "r")],
                             [x, y, z, bottom])
            self.assertEqual(q(r["association_coordinate"]["delta"]), delta)
            self.assertEqual(q(r["association_coordinate"]["kappa_min"]), max(0, x+y-bottom))
            self.assertEqual(q(r["association_coordinate"]["kappa_max"]), min(x, y))
            self.assertEqual(q(r["residuals"]["fiber_width"]), min(x, y, bottom-x, bottom-y))
            self.assertEqual(r["association_coordinate"]["conditional_endpoint_independent"],
                             delta == 0 if bottom else None)
            self.assertEqual(q(r["residuals"]["J_f"]), 1)
            completion = [q(x) for x in r["association_coordinate"]["product_completion"]]
            self.assertEqual(sum(completion), 1)
            self.assertTrue(all(x >= 0 for x in completion))
            rf = r["residuals"]["R_f"]["value"]
            self.assertEqual(q(rf), p[3] - completion[3])
            m = p[2] + p[3] + p[4]
            if m:
                self.assertEqual(q(r["residuals"]["R_guard"]["value"]),
                                 (p[3] - completion[3])/m)
            else:
                self.assertIsNone(r["residuals"]["R_guard"]["value"])



if __name__ == "__main__":
    BINARY = Path(sys.argv.pop(1)).resolve()
    result = unittest.main(verbosity=2, exit=False).result
    print("[PASS] AuricFibFiniteAnalysis" if result.wasSuccessful() else "[FAIL] AuricFibFiniteAnalysis")
    sys.exit(0 if result.wasSuccessful() else 1)
