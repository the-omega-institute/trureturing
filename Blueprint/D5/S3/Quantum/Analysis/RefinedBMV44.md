# The refined BMV comparisons with four copies of each factor

## Abstract

The refined BMV comparisons with four copies of each factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV44.product_bound44`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV44.product_bound44` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-44-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV44.product_bound44`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-44-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV44.product_bound44","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices A and B, the mean trace of the seventy words with four copies of each factor is at least the trace of (AB)^4. The dimensions and ranks are arbitrary. Combining the cyclic word classes with the fourth moment of the Hermitian part of AB gives an exact decomposition into nonnegative trace differences. The terms come from weighted commutator squares, Frobenius squares, and unitary triangularization. This proves the product comparison E(4,4) of Hägele's Section 1, whose three-dimensional case is named in Section 7.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV44.exponential_bound44`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV44.exponential_bound44` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the same mean for exp H and exp K is at least the trace of exp(4H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter argument of Hägele's Lemma 2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV44.exponential_bound44`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV44.product_bound44`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43](RefinedBMV43.md)
