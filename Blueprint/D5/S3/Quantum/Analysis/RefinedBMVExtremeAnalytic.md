# The refined BMV lower bound at first degrees five through seven in every finite dimension

## Abstract

The refined BMV lower bound at first degrees five through seven

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

**Theorem 1.3 (Six copies of the first factor).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices A and B in any finite dimension, the mean trace of the 84 words with six copies of A and three of B is at least the trace of the cube of A^(6/3) B. The first matrix may be singular and may have any number of distinct eigenvalues. The exact coefficient signs at this degree give positive semidefiniteness of the normalized upper kernel by the finite interval Gram argument. The cyclic decomposition and Schur product then give the trace inequality.

**Theorem 1.4 (The exponential comparison at degree six).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For complex Hermitian H and K in any finite dimension, the same word mean on exp H and exp K is bounded below by the trace of exp(6H + 3K). Apply the product comparison to the two exponentials and then use the dyadic trace comparison from Hägele's Lemma 2.

**Theorem 1.5 (Seven copies of the first factor).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices A and B in any finite dimension, the mean trace of the 120 words with seven copies of A and three of B is at least the trace of the cube of A^(7/3) B. The first matrix may be singular and may have any number of distinct eigenvalues. The exact coefficient signs at this degree give positive semidefiniteness of the normalized upper kernel by the finite interval Gram argument. The cyclic decomposition and Schur product then give the trace inequality.

**Theorem 1.6 (The exponential comparison at degree seven).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For complex Hermitian H and K in any finite dimension, the same word mean on exp H and exp K is bounded below by the trace of exp(7H + 3K). Apply the product comparison to the two exponentials and then use the dyadic trace comparison from Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_five`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_seven`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_six`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_five`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_seven`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_six`
