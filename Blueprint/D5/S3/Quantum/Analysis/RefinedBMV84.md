# The refined BMV comparisons with eight copies of the first factor

## Abstract

The refined BMV comparisons with eight copies of the first factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV84.product_bound84`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV84.product_bound84` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-84-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV84.product_bound84`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-84-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV84.product_bound84","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any finite complex positive semidefinite A and B, the mean of the 495 word traces with eight copies of A and four of B is at least the trace of (A^2 B)^4. Three rational Gram blocks compare the mean with the fourth trace of the Hermitian part of A^(3/2) B A^(1/2). The quartic trace comparison then bounds the balanced product. The proof treats singular A directly.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV84.exponential_bound84`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV84.exponential_bound84` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the trace of exp(8H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV84.exponential_bound84`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV84.product_bound84`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV44](RefinedBMV44.md)
