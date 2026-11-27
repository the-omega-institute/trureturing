# Covariance-root converse on null diamonds

## Abstract

A lower bound for normalized covariance roots and divergence of their harmonic trace.

Equation (71) of Satishchandran and Sorce tests the trace of a squared root difference. The operator estimate here controls the original perturbation by that difference. A uniform lower bound for the radial perturbations then passes to the angular trace.

**Definition 1.1 (Covariance normalizer).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceNormalizer`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceNormalizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the ring inverse of the positive root of the normalization operator.

**Definition 1.2 (Normalized root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceRootDiff`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceRootDiff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take positive roots after conjugating both covariances by the same inverse square root, then subtract the reference root.

**Theorem 1.3 (Perturbed norm bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_B_prime_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_B_prime_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The order bound for the perturbed covariance is twice the normalization operator. The congruence sends that upper bound to twice the identity.

**Theorem 1.4 (Reference norm bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_A_prime_le_two_div_c`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_A_prime_le_two_div_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Coercivity bounds twice the identity above by two over the coercivity constant times the normalization operator. Conjugating gives the same scalar bound on the reference norm.

**Theorem 1.5 (Noncommutative difference of squares).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.congruence_diff_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.congruence_diff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Place the perturbed root on the left of the root difference and the reference root on its right. The cross terms cancel in their original order.

**Theorem 1.6 (Hilbert–Schmidt converse).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_congruence_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_congruence_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The ideal inequalities bound left and right multiplication by the respective operator norms. Undoing the congruence costs the norm of the normalization operator. The exact constant multiplies that norm by the sum of the square roots of two and two over coercivity.

**Theorem 1.7 (Common sum-norm converse).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_sum_norm_converse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_sum_norm_converse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Adding the identity to the normalizer raises the coercivity constant by one and preserves domination of the perturbed covariance by twice the new normalizer.

**Theorem 1.8 (Obstruction in one block).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_sqrt_diff_of_not_hs_T`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_sqrt_diff_of_not_hs_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A perturbation outside the Hilbert–Schmidt ideal forces the normalized root difference outside that ideal.

**Theorem 1.9 (Two-sided block comparison).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.quarterPower_block_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.quarterPower_block_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A Hilbert–Schmidt quarter-power factor yields a finite upper estimate for each root difference. The converse bounds the perturbation from this same normalized difference.

**Definition 1.10 (Uniform block hypotheses).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.ConverseBlockBounds`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.ConverseBlockBounds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The positive harmonic degrees share a lower coercivity constant, an upper normalizer norm, the covariance order bounds, and a positive lower amplitude with the two angular factors.

**Definition 1.11 (Harmonic trace contribution).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converseModeWeight`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converseModeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The contribution of a positive degree is its harmonic multiplicity times the squared Hilbert–Schmidt norm of its normalized radial root difference.

**Theorem 1.12 (Six-dimensional cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D6`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For Hilbert–Schmidt radial root differences, the trace through degree L is bounded below by a positive multiple of log L for L at least two.

**Theorem 1.13 (Higher-dimensional cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D_ge_7`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D_ge_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For Hilbert–Schmidt radial root differences, the trace through degree L is bounded below by a positive multiple of L to the power D minus six.

**Theorem 1.14 (Divergence of the harmonic trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_eq71_diverges_of_D_ge_6`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_eq71_diverges_of_D_ge_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D at least six the lower cutoff bounds tend to infinity. The individual positive-degree trace contributions form a nonsummable sequence.

**Theorem 1.15 (Block-diagonal operator obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_eq71_operator_of_D_ge_6`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_eq71_operator_of_D_ge_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If the ambient root difference were Hilbert–Schmidt, restricting its basis sum to orthogonal copies of the radial modes would give a finite weighted sum. Positive multiplicity makes each radial mode Hilbert–Schmidt, and the cutoff bounds contradict summability.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.ConverseBlockBounds`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.congruence_diff_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converseModeWeight`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_eq71_diverges_of_D_ge_6`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D6`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.converse_partial_trace_bounds_D_ge_7`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceNormalizer`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.covarianceRootDiff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_congruence_lower_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.hs_sum_norm_converse`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_A_prime_le_two_div_c`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.norm_B_prime_le_two`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_eq71_operator_of_D_ge_6`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.not_hs_sqrt_diff_of_not_hs_T`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.quarterPower_block_comparison`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold](NullDiamondDimensionThreshold.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../TraceClass/HilbertSchmidt.md)
