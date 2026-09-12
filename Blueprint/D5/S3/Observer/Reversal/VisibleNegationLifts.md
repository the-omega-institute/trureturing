# Visible Negation Lifts

## Abstract

All involutive lifts of visible negation are classified by idempotents in the observation kernel.

**Definition 1.1 (fixedPart).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart`

*Formalization.* `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing canonical fixed summand, packaged as a linear map.

**Theorem 1.2 (fixedPart idempotent).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical fixed summand is an idempotent.

**Theorem 1.3 (fixedPart in observation kernel).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_in_observation_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_in_observation_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A visible minus sign annihilates the entire fixed summand.

**Theorem 1.4 (visible negation iff hidden idempotent).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.visible_negation_iff_hidden_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/VisibleNegationLifts.visible_negation_iff_hidden_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every involution lifting the observed minus sign has a hidden idempotent representation. The converse constructs the involution law; uniqueness is the separate theorem below.

**Theorem 1.5 (hidden idempotent unique).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.hidden_idempotent_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/VisibleNegationLifts.hidden_idempotent_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden idempotent is determined by the full involution, even though it is invisible to the original observation.

**Definition 1.6 (visibleReflection).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection`

*Formalization.* `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reverse the retained subspace and preserve the complementary subspace.

**Theorem 1.7 (visibleReflection spec).**

Lean statement: `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A projection induces a genuine state involution with visible action -I.

## References

- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_idempotent`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.fixedPart_in_observation_kernel`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.hidden_idempotent_unique`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.visibleReflection_spec`
- Truth anchor: `D5/S3/Observer/Reversal/VisibleNegationLifts.visible_negation_iff_hidden_idempotent`
- Dependency: [D5/S0/Conventions/InvolutionDecomposition](../../../S0/Conventions/InvolutionDecomposition.md)
