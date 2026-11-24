# Hägele's refined BMV lower bounds at (6,4) and (7,4)

## Abstract

Hägele's refined BMV lower bounds at (6,4) and (7,4)

**Theorem 1.1 (Product comparison at (6,4)).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound64`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound64` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-64-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound64`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-64-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV67.product_bound64","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For finite complex positive semidefinite A and B, the mean trace of the 210 words dominates the trace of (A^(3/2) B)^4. The proof compares the mean with the balanced integer word through three rational Gram matrices. The third block places B on both sides of each pair of half words.

**Theorem 1.2 (Product comparison at (7,4)).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound74`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound74` (`✓ std3`). ∎

*Resolves.* `Problems/hagele-2026-refined-bmv-74-all-dimensions` (proved) by `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound74`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hagele-2026-refined-bmv-74-all-dimensions","declaration_gid":"D5/S3/Quantum/Analysis/RefinedBMV67.product_bound74","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For finite complex positive semidefinite A and Hermitian B, the mean trace of the 330 words dominates the trace of (A^(7/4) B)^4. A rational Gram certificate weighted by A gives the integer comparison. Fourth-root powers and three Frobenius estimates give the fractional-power comparison for singular and invertible A.

**Theorem 1.3 (Exponential comparison at (6,4)).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound64`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the mean for exp H and exp K is at least the trace of exp(6H + 4K). The dyadic Lie–Trotter limit gives the comparison.

**Theorem 1.4 (Exponential comparison at (7,4)).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound74`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound74` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K, the mean for exp H and exp K is at least the trace of exp(7H + 4K). The dyadic Lie–Trotter limit gives the comparison.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound64`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV67.exponential_bound74`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound64`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV67.product_bound74`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV54](RefinedBMV54.md)
