# The refined BMV lower bound for three letters of each kind

## Abstract

The refined BMV lower bound for three letters of each kind

**Theorem 1.1 (The refined BMV lower bound for three letters of each kind).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-33-dimension-four` (proved) by `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-33-dimension-four","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

The inequality holds for every pair of complex Hermitian four-by-four matrices. A trace-power comparison and the Lie–Trotter limit connect the cubic moment bound to the exponential trace.

**Theorem 1.2 (The lower bound in every finite dimension).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33_all` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-33-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33_all`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-33-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33_all","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For arbitrary finite complex Hermitian matrices, the twenty-word mean dominates the exponential trace. The general product bound and the dyadic Lie–Trotter comparison prove the claim.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33_all`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV33](RefinedBMV33.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVTracePower](RefinedBMVTracePower.md)
- Dependency: [D5/S3/Quantum/Analysis/TrotterProduct](TrotterProduct.md)
