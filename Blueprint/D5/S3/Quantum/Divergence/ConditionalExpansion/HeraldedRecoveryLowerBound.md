# Heralded recovery lower bound

## Abstract

Finite heralded exact recovery gives a universal conditional trace-gap comparison.

**Theorem 1.1 (Contrast lower bound from a heralded exact branch).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_contrast_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_contrast_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a finite quantum channel, K a finite Kraus family with effect sum KⱼᴴKⱼ ≤ I, and p ∈ [0,1]. If the Kraus branch sends act N(X) to pX for every matrix X, then every Hermitian amplified test H satisfies p times the positive-trace contrast of H over its reference marginal is at most the corresponding contrast after amp N. The proof includes the failure branch I − sum KⱼᴴKⱼ and uses positive-part trace monotonicity.

**Theorem 1.2 (Coefficient comparison).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_coefficient_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_coefficient_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite channel N on input dimension d ≥ 2, let pRec be the supremum of finite trace-nonincreasing Kraus recovery weights and η the infimum of the admissible conditional ratios. For every γ ≥ 1 and either orthogonality flag, pRec ≤ η ≤ d² pRec. Moreover η is positive exactly when some admissible recovery has positive weight.

The coefficient uses the conditional expansion of Hirche, George, Nuradha and Wilde, arXiv:2608.27171v1, Eq. (2.42). Bény and Oreshkov's postprocessing duality, arXiv:1103.0649v3, Theorem 2, gives the complementary-channel characterization of exact recovery.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_coefficient_comparison`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound.heralded_recovery_contrast_lower_bound`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](../CompleteHockeyStickRefutation.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound](HeraldedRecoveryUpperBound.md)
