# The refined BMV lower bound at (16,4)

## Abstract

The refined BMV lower bound at (16,4)

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.product_bound164`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.product_bound164` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-164-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.product_bound164`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-164-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.product_bound164","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite A and Hermitian B in any finite complex dimension, the mean real trace of the 4845 ordered words with sixteen copies of A and four of B dominates the real trace of (A^4 B)^4. Two rational Gram matrices weighted by the identity and A compare the word mean with the fourth trace of the Hermitian part obtained by centering the exponents of the two phase factors. The comparison includes singular A.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.exponential_bound164`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.exponential_bound164` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the word mean for exp H and exp K dominates the trace of exp(16H + 4K) by the dyadic trace-power comparison.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.exponential_bound164`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.product_bound164`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV67](../RefinedBMV67.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV84](../RefinedBMV84.md)
