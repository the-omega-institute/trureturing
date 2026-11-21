# The refined BMV (5,3) lower bound in every finite dimension

## Abstract

The refined BMV (5,3) lower bound in every finite dimension

**Theorem 1.1 (The spectral-power trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_five`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any pair of positive semidefinite complex matrices A and B in any finite dimension, the mean trace of the 56 words with five copies of A and three copies of B is at least the trace of the cube of A^(5/3) B, where the power of A is defined by spectral calculus. The repository proof uses the eigenvalues of the positive semidefinite cube root of A and splits the cubic trace defect into a cyclic sum of centered kernels. Exact polynomial certificates supply the mixed derivative and boundary signs that make the rectangle differences of the normalized upper kernel nonnegative on each sorted finite sample. The differences telescope, giving a sum of weighted outer products of interval indicators. Diagonal rescaling and a rank-one block below the center give positive semidefinite centered matrices. The Schur product theorem makes each centered walk contribution nonnegative.

**Theorem 1.2 (The exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_five`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any finite-dimensional complex Hermitian pair H and K, the mean trace of the 56 words with five copies of the exponential of H and three copies of the exponential of K is at least the trace of the matrix exponential of 5H + 3K. Hägele raises the lower-bound question in Section 7. The product bound for the two exponentials and the dyadic Lie–Trotter trace comparison from Hägele's Lemma 2 give the result.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_five`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_five`
