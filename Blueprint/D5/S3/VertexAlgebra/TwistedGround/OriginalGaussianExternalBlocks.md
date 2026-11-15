# Actual Corrected and Inverse-right External Gaussian Blocks

## Abstract

Actual Corrected and Inverse-right External Gaussian Blocks

The left row is the literal damped correctedMatrix restricted to a frequency box and any finite external family. The right row is its actual transport by sourceBlock of the inverse frequency Gram boxMatrix. Arbitrary input and output modes, all colours and empty finite supports are included.

Expanding these arrays gives internal blocks G tensor D K D and G inverse tensor D inverse K D inverse. The nondegenerate symmetric Gram and nonzero frequency roots give both ordered inverse similarities to the finite square resolvent. This algebra needs no Gram square-root construction or separate raw-block contraction hypothesis.

Substitution into FiniteGaussianSewing.effectiveKernel gives equal diagonal blocks G times the free input-output covariance plus B_J, cross block minus G times B_T, and its ordinary transpose. Uniform signed and square cutoff estimates and the external l1 bounds prove locally uniform convergence on every smaller complex disk.

The effectiveKernel definition is used algebraically; finite_sewing is not applied outside its raw contraction hypotheses. This covariance theorem makes no claim of raw full-disk occupation summability, source energy coefficient extraction, Laurent selectors, theta averaging, identityK or C1.

**Theorem 1.1 (root_units).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.root_units`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.root_units` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frequency square-root diagonal matrix and its reciprocal multiply to the identity in both orders, including the empty frequency box.

**Definition 1.2 (originalRow).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalRow`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The originalRow definition fixes the literal objects and conventions used in the proof.

**Definition 1.3 (inverseSubstitution).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.inverseSubstitution`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.inverseSubstitution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverseSubstitution definition fixes the literal objects and conventions used in the proof.

**Definition 1.4 (leftRow).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.leftRow`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.leftRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leftRow definition fixes the literal objects and conventions used in the proof.

**Definition 1.5 (rightRow).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.rightRow`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.rightRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rightRow definition fixes the literal objects and conventions used in the proof.

**Definition 1.6 (originalEffectiveKernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalEffectiveKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalEffectiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The originalEffectiveKernel definition fixes the literal objects and conventions used in the proof.

**Definition 1.7 (explicitEffectiveKernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.explicitEffectiveKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.explicitEffectiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicitEffectiveKernel definition fixes the literal objects and conventions used in the proof.

**Theorem 1.8 (original_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_source statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.9 (original_inverse_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_inverse_source statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.10 (original_internal_inverse_similarities).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_internal_inverse_similarities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_internal_inverse_similarities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_internal_inverse_similarities statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.11 (original_mixed).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_mixed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.12 (original_inverse_mixed).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_inverse_mixed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.13 (original_mixed_transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_mixed_transpose statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.14 (cutoff_zeroExtend).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.cutoff_zeroExtend`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.cutoff_zeroExtend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff_zeroExtend statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.15 (external_pair_error).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.external_pair_error`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.external_pair_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The external_pair_error statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

**Theorem 1.16 (original_effectiveKernel_blocks_tendsto_explicit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original_effectiveKernel_blocks_tendsto_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.cutoff_zeroExtend`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.explicitEffectiveKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.external_pair_error`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.inverseSubstitution`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.leftRow`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalEffectiveKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalRow`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_internal_inverse_similarities`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_mixed`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_source`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.rightRow`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.root_units`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent](OriginalGaussianExternalResolvent.md)
