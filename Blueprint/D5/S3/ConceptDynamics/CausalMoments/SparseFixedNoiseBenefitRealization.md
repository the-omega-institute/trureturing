# Sparse fixed-noise benefit realization

## Abstract

Compress the two complete table laws separately and retain their product semantics. The full selected-pair response distribution is unchanged, so every previously attainable benefit value has a sparse independent witness.

**Theorem 1.1 (Separate compression preserves the selected law).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.exists_fixedNoise_sparse_equivalent`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.exists_fixedNoise_sparse_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both mechanisms retain every complete row marginal. Each has at most 3k+1 nonzero table atoms, and the joint distribution of the covariate and selected responses remains equal.

**Theorem 1.2 (Bound the product disturbance support).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_pair_support_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_pair_support_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of the rational product law is the Cartesian product of the component supports. The two-mechanism support is at most the square of 3k+1; the covariate root is separate.

**Theorem 1.3 (Preserve the entire attainable query image).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_attainment_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_attainment_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target with the four prescribed conditional intervention marginals is attainable exactly when it is attainable with both table support bounds. No extra cross-stratum constraints are supplied.

**Theorem 1.4 (Sparse attaining witnesses for the sharp interval).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_joint_benefit_sharp_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_joint_benefit_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composes the prior weighted-product sharp interval theorem with the new same-model-family support reduction. The interval, marginal conditions, and benefit definition are unchanged.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.exists_fixedNoise_sparse_equivalent`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_pair_support_card_le`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_attainment_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.fixedNoise_sparse_joint_benefit_sharp_iff`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds](FixedNoiseCovariateBenefitSharpBounds.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments](ReducedResponseTableMoments.md)
