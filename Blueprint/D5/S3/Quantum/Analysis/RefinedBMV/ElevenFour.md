# The refined BMV lower bound at (11,4)

## Abstract

The refined BMV lower bound at (11,4)

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.product_bound114`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.product_bound114` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-114-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.product_bound114`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-114-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.product_bound114","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite A and Hermitian B in any finite complex dimension, the mean of the real traces of the 1365 words with eleven copies of A and four of B dominates the real trace of (A^(11/4) B)^4. One rational Gram matrix weighted by A compares the word mean with the cyclic word with gaps (3,3,2,3). Two trace inequalities give the fractional-power comparison.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.exponential_bound114`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.exponential_bound114` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the corresponding mean for exp H and exp K dominates the trace of exp(11H + 4K), by the dyadic trace-power comparison.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.exponential_bound114`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.product_bound114`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
