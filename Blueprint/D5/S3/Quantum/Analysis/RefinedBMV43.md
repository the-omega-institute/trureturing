# The refined BMV lower bound for four and three factors

## Abstract

The refined BMV lower bound for four and three factors

**Theorem 1.1 (The trace-power bound in every finite dimension).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV43.E43_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV43.E43_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

The trace comparison uses the positive spectral power of the first factor. Diagonalizing its cube root turns the trace defect into a sum of centered quadratic forms, each nonnegative by the Schur product theorem.

**Theorem 1.2 (The exponential lower bound in every finite dimension).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV43.L43_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV43.L43_all` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-43-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV43.L43_all`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-43-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV43.L43_all","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For any finite complex Hermitian pair, the 35-word mean dominates the exponential trace. The dyadic trace-power comparison applies after scaling the first Hermitian factor by four thirds.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV43.E43_all`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV43.L43_all`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43Kernel](RefinedBMV43Kernel.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVLowerBound](RefinedBMVLowerBound.md)
