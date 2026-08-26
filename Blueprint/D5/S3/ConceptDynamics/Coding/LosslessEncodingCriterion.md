# Lossless Encoding Criterion

## Abstract

An encoding is lossless on a sender exactly when it is injective on the coordinates that sender realizes.

**Theorem 1.1 (Losslessness is injectivity on the sender image).**

$$\forall X \in Type, S \in Type, M \in Type, sender \in X \to S, encoder \in S \to M,\; \operatorname{InjOn}\left(encoder, \operatorname{range}\left(sender\right)\right) \Leftrightarrow \left(\forall x \in X, y \in X,\; \operatorname{messageConcept}\left(sender, encoder, x\right) = \operatorname{messageConcept}\left(sender, encoder, y\right) \Leftrightarrow sender\left(x\right) = sender\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.lossless_iff_injective_on_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only source coordinates that the sender actually realizes matter. The encoder is injective on that image exactly when two states have the same encoded message precisely when they already have the same sender coordinate.

Injectivity prevents the encoder from merging distinct realized coordinates. Conversely, equality reflection for every pair of states proves injectivity by choosing witnesses for the two coordinates in the sender image.

**Lemma 1.2 (Noninjectivity is exactly a collapsed sender distinction).**

$$\forall X \in Type, S \in Type, M \in Type, sender \in X \to S, encoder \in S \to M,\; \left(\neg \operatorname{InjOn}\left(encoder, \operatorname{range}\left(sender\right)\right)\right) \Leftrightarrow \left(\exists x \in X, y \in X,\; \operatorname{messageConcept}\left(sender, encoder, x\right) = \operatorname{messageConcept}\left(sender, encoder, y\right) \land sender\left(x\right) \ne sender\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.not_injective_on_image_iff_strictly_coarser` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Failure of injectivity on the realized sender image is equivalent to a pair of states with one message but different sender coordinates. Thus the abstract injectivity failure is exactly a concrete distinction that the encoding erases.

**Lemma 1.3 (The importance of a lost distinction depends on the target).**

$$\forall X \in Type, S \in Type, M \in Type, sender \in X \to S, encoder \in S \to M,\; \left(\neg \operatorname{InjOn}\left(encoder, \operatorname{range}\left(sender\right)\right)\right) \Rightarrow \left(\operatorname{Refines}\left(\operatorname{messageConcept}\left(sender, encoder\right), \operatorname{messageConcept}\left(sender, encoder\right)\right) \land \left(\neg \operatorname{Refines}\left(sender, \operatorname{messageConcept}\left(sender, encoder\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.lost_distinction_importance_depends_on_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lossy encoder, the message remains recoverable from itself by the identity map, so it is still a decidable target of the message readout.

The sender's full concept cannot factor through that same message. A factor map would assign equal sender coordinates to the collapsed pair supplied by noninjectivity, contradicting that the pair was a genuine sender distinction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.lossless_iff_injective_on_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.lost_distinction_importance_depends_on_target`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.not_injective_on_image_iff_strictly_coarser`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
