# The refined BMV comparisons with five copies of the first factor

## Abstract

The refined BMV comparisons with five copies of the first factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV54.product_bound54`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV54.product_bound54` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-54-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV54.product_bound54`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-54-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV54.product_bound54","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any finite complex positive semidefinite A and Hermitian B, the mean of the 126 word traces with five copies of A and four of B is at least the trace of (A^(5/4) B)^4. The weighted sum of four Frobenius squares compares the mean with the trace of A(AB)^4. Three further commutator and adjoint squares give the fractional-power comparison. The proof treats singular A directly.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV54.exponential_bound54`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV54.exponential_bound54` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the trace of exp(5H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV54.exponential_bound54`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV54.product_bound54`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV44](RefinedBMV44.md)
