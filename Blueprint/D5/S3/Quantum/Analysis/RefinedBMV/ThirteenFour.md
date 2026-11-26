# The refined BMV comparisons with thirteen copies of the first factor

## Abstract

The refined BMV comparisons with thirteen copies of the first factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.product_bound134`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.product_bound134` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

In every finite complex dimension, for positive semidefinite A and Hermitian B, the mean of the real parts of the 2,380 ordered word traces with thirteen copies of A and four of B is at least the real part of the trace of (A^(13/4) B)^4. A rational positive semidefinite Gram matrix on 28 half-words, weighted by A, compares the mean with the real part of the trace of the word with cyclic gaps (4,3,3,3). Two trace Cauchy–Schwarz inequalities bound the fractional-power trace by that word trace. The argument allows singular A.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.exponential_bound134`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.exponential_bound134` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the real part of the trace of exp(13H + 4K). The fourth trace-power comparison uses the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.exponential_bound134`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour.product_bound134`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
