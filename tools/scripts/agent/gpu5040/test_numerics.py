"""Bounded CPU cross-checks. This module never allocates an MPS tensor."""

import itertools
import math
import unittest

import numpy as np
import torch

from positive_control import positive_control56
from tensor_core import OCCUPATION, OccupationDP, gram_error, householder_frame, normalize, verify_full_output


class NumericalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        torch.set_num_threads(1)

    def test_occupation_dp_agrees_with_independent_brute_words(self):
        rng = np.random.default_rng(104729)
        for dimension, occupation in ((3, (2, 1, 1, 0)), (2, OCCUPATION)):
            frame, _ = np.linalg.qr(rng.normal(size=(4 * dimension, dimension)))
            matrices = frame.reshape(4, dimension, dimension)
            initial = rng.normal(size=dimension)
            initial /= np.linalg.norm(initial)
            expected = np.zeros_like(initial)
            count = 0
            for word in itertools.product(range(4), repeat=sum(occupation)):
                if tuple(word.count(i) for i in range(4)) == occupation:
                    vector = initial.copy()
                    for label in word:
                        vector = matrices[label] @ vector
                    expected += vector
                    count += 1
            expected /= math.sqrt(count)
            actual = OccupationDP(occupation)(torch.from_numpy(matrices), torch.from_numpy(initial)).numpy()
            np.testing.assert_allclose(expected, actual, rtol=0, atol=2e-13)

    def test_householder_and_target_gradients(self):
        rng = np.random.default_rng(104729)
        h = torch.tensor(rng.normal(size=(2, 8)), dtype=torch.float64, requires_grad=True)
        v = torch.tensor(rng.normal(size=2), dtype=torch.float64, requires_grad=True)
        dp = OccupationDP()

        def loss(reflectors, initial):
            target = dp(householder_frame(reflectors).reshape(4, 2, 2), normalize(initial, 0))
            return 1 - target.square().sum()

        self.assertTrue(torch.autograd.gradcheck(loss, (h, v), eps=1e-6, atol=1e-6, rtol=1e-4))
        self.assertLess(float(gram_error(householder_frame(h).reshape(4, 2, 2)).detach()), 2e-14)

    def test_direct_56d_positive_control_and_unchanged_verifier(self):
        matrices, initial = positive_control56()
        target = OccupationDP()(torch.from_numpy(matrices), torch.from_numpy(initial))
        self.assertAlmostEqual(1, float(target @ target), delta=2e-13)
        full = verify_full_output(matrices, initial, chunk_size=256)
        self.assertEqual(65536, full["full_words"])
        self.assertEqual(840, full["legal_words"])
        self.assertAlmostEqual(1, full["norm"], delta=2e-13)
        self.assertAlmostEqual(1, full["target_fidelity"], delta=2e-13)
        self.assertLess(full["target_separated_memory_residual_l2"], 2e-13)
        self.assertLess(full["gram_max_abs_error"], 2e-14)
        altered = matrices * 1.001
        before = altered.tobytes()
        disagreement = verify_full_output(altered, initial)
        self.assertGreater(disagreement["norm"], 1.007)
        self.assertGreater(disagreement["gram_max_abs_error"], 0.002)
        self.assertEqual(before, altered.tobytes())


if __name__ == "__main__":
    unittest.main()
