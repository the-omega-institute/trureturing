# Relative Complement

## Abstract

Relative complement is universe-indexed; pullbacks preserve it, images may fail.

**Theorem 1.1 (Pullback preserves relative complement).**

$$\operatorname{preimage}\left(q, \operatorname{relativeComplement}\left(U, A\right)\right) = \operatorname{relativeComplement}\left(\operatorname{preimage}\left(q, U\right), \operatorname{preimage}\left(q, A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/RelativeComplement.preimage_relativeComplement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any readout, pulling back the complement of a subset inside a chosen ambient region equals the complement of the pulled-back subset inside the pulled-back ambient region.

The equality is definitional: inverse image preserves both membership in the ambient set and exclusion from the subset without any injectivity or surjectivity assumption.

**Theorem 1.2 (Direct image can fail to preserve complement).**

$$\operatorname{image}\left(fst, \operatorname{complement}\left(\operatorname{singleton}\left(\operatorname{pair}\left(false, false\right)\right)\right)\right) \neq \operatorname{complement}\left(\operatorname{image}\left(fst, \operatorname{singleton}\left(\operatorname{pair}\left(false, false\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/RelativeComplement.image_complement_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The counterexample uses first projection from a Boolean pair and the singleton containing the all-false pair. Its complement still contains a point whose first coordinate is false.

Consequently false belongs to the image of the complement, while it does not belong to the complement of the singleton image. Even this finite surjective map therefore fails to commute with direct image complementation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/RelativeComplement.image_complement_counterexample`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/RelativeComplement.preimage_relativeComplement`
