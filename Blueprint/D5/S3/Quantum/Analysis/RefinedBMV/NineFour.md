# The refined BMV comparisons with nine copies of the first factor

## Abstract

The refined BMV comparisons with nine copies of the first factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.product_bound94`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.product_bound94` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-94-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.product_bound94`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-94-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV/NineFour.product_bound94","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

In every finite complex dimension, for positive semidefinite A and Hermitian B, the mean of the 715 word traces with nine copies of A and four of B is at least the trace of (A^(9/4) B)^4. One rational positive semidefinite Gram matrix on 15 half-words, weighted by A, compares the mean with the word trace with gaps (3,2,2,2). Two trace Cauchy–Schwarz inequalities then give the balanced bound. The argument allows singular A.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.exponential_bound94`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.exponential_bound94` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the trace of exp(9H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.exponential_bound94`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/NineFour.product_bound94`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
