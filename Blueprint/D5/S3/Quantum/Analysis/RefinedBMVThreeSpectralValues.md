# Refined BMV lower bounds with three spectral values

## Abstract

Refined BMV lower bounds with three spectral values

**Theorem 1.1 (The three-label inequality for positive matrix factors).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.operator_walk_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.operator_walk_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

Cyclicity and conjugate reversal pair the mixed terms. At each of the three labels, Hilbert–Schmidt Cauchy–Schwarz and the arithmetic–geometric mean bound the mixed trace by the two repeated-label traces with their coefficient weights.

**Theorem 1.2 (The strong product bound).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any two finite-dimensional positive semidefinite complex matrices, with at most three distinct eigenvalues of the first matrix, the mean trace of the words with five, six, or seven first factors and three second factors is at least the trace of the cube of the product using spectral power p/3 of the first matrix. The square root of the second matrix compresses each spectral projection into a positive factor. The three-label pairing uses the scalar coefficient certificate for the ordered eigenvalue cube roots.

**Theorem 1.3 (The exponential lower bound).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.exponential_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any finite-dimensional Hermitian pair whose first matrix has at most three distinct eigenvalues, the same word counts applied to the matrix exponentials give a lower bound by the trace of the exponential of p times the first matrix plus three times the second matrix. The exact dyadic Lie–Trotter comparison connects the cube estimate to this exponential, as in Hägele's Lemma 2. Section 7 discusses the case with five first factors.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.exponential_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.operator_walk_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.product_bound`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVDimThree](RefinedBMVDimThree.md)
