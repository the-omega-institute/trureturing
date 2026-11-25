# The refined BMV comparisons with ten copies of the first factor

## Abstract

The refined BMV comparisons with ten copies of the first factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.product_bound104`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.product_bound104` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-104-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.product_bound104`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-104-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV/TenFour.product_bound104","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

In every finite complex dimension, for positive semidefinite A and B, the mean of the 1001 word traces with ten copies of A and four of B is at least the trace of (A^(5/2) B)^4. Three rational positive semidefinite Gram blocks of sizes 21, 15 and 6, with weights I/I, A/A and B/B, compare the mean with the word trace with gaps (3,2,3,2). Trace Cauchy–Schwarz gives the fractional-power bound. The argument allows singular A and B.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.exponential_bound104`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.exponential_bound104` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the trace of exp(10H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.exponential_bound104`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/TenFour.product_bound104`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
