# The refined BMV lower bound at (12,4)

## Abstract

The refined BMV lower bound at (12,4)

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.product_bound124`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.product_bound124` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-124-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.product_bound124`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-124-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.product_bound124","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite A and Hermitian B in any finite complex dimension, the mean real trace of the 1820 ordered words with twelve copies of A and four of B dominates the real trace of (A^3 B)^4. Two rational Gram matrices weighted by the identity and A compare the word mean with the fourth trace of the Hermitian part of A B A^2. The Hermitian-part comparison includes singular A.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.exponential_bound124`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.exponential_bound124` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the word mean for exp H and exp K dominates the trace of exp(12H + 4K) by the dyadic trace-power comparison.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.exponential_bound124`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.product_bound124`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
