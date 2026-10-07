"""Behavior tests for exact two-reading searches. License: Apache-2.0."""
import unittest
from fractions import Fraction
from phase_readout import analyze, finite_model, pell_rows


class PhaseReadoutTests(unittest.TestCase):
    def test_fibonacci_rational_states_keep_only_sign_collisions(self):
        model = {"matrix": [["0", "1"], ["1", "1"]],
                 "states": [[str(a), str(b)] for a in range(-3, 4)
                            for b in range(-3, 4)]}
        result = analyze(model)
        self.assertEqual(result["discriminant"], "5")
        self.assertEqual(result["extra_collision_buckets"], 0)
        self.assertEqual(result["readout_buckets"], 25)

    def test_scalar_and_split_updates_have_real_rational_collisions(self):
        for matrix in ([["1", "0"], ["0", "1"]],
                       [["1", "0"], ["0", "2"]]):
            result = analyze({"matrix": matrix,
                              "states": [["1", "1"], ["1", "-1"]]})
            self.assertEqual(result["extra_collision_buckets"], 1)
            self.assertEqual(result["collision"]["pair"], [["1", "1"], ["1", "-1"]])

    def test_nonsplit_and_split_finite_domains(self):
        for p, expected in ((3, 0), (7, 0), (11, 1), (5, 1)):
            result = analyze(finite_model(p))
            self.assertEqual(result["extra_collision_buckets"] > 0, bool(expected))
        self.assertEqual(analyze(finite_model(3))["readout_buckets"], 5)

    def test_exact_rational_noninteger_input(self):
        r = analyze({"matrix": [["0", "1"], ["1", "1"]],
                     "states": [["1/2", "1/3"], ["-1/2", "-1/3"]]})
        self.assertEqual(r["extra_collision_buckets"], 0)
        self.assertEqual(r["readout_buckets"], 1)

    def test_malformed_and_nonprime_inputs_are_rejected(self):
        base = {"matrix": [["0", "1"], ["1", "1"]], "states": [["1", "0"]]}
        for model in ({**base, "states": "10"},
                      {**base, "matrix": [["1"], ["0", "1"]]},
                      {**base, "states": [["1/0", "0"]]},
                      {**base, "states": [["1", "0"], ["1", "0"]]},
                      {**base, "modulus": 9}):
            with self.assertRaises(ValueError):
                analyze(model)

    def test_pell_near_collisions_are_exact_and_separated(self):
        rows = pell_rows(8)
        self.assertEqual((rows[0]["p"], rows[0]["q"]), (9, 4))
        for n, row in enumerate(rows, 1):
            p, q = row["p"], row["q"]
            self.assertEqual(p*p-5*q*q, 1)
            self.assertGreaterEqual(p, 9**n)
            self.assertEqual(Fraction(row["readout_error"]), Fraction(1, p*p))
            self.assertEqual(Fraction(row["target_gap"]), 1-Fraction(q*q, p*p))
            self.assertGreater(Fraction(row["target_gap"]), Fraction(4, 5))


if __name__ == "__main__":
    unittest.main()
