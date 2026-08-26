# Concept-Relative Identity

## Abstract

Concept-relative identity is an equivalence relation and can identify strictly more pairs than equality.

**Lemma 1.1 (Concept-relative identity is an equivalence relation).**

$$\forall X \in Type, C \in Type, q \in X \to C,\; \operatorname{Equivalence}\left(\operatorname{ConceptIdentity}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity.concept_identity_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept readout partitions its source into fibers of equal observed value. Belonging to the same fiber is reflexive, symmetric, and transitive, so it defines an equivalence relation on the source objects.

**Theorem 1.2 (Concept-relative identity can be strictly coarser than equality).**

$$\left(\forall X \in Type, C \in Type, q \in X \to C, x \in X, y \in X,\; x = y \Rightarrow \operatorname{ConceptIdentity}\left(q, x, y\right)\right) \land \left(\exists q \in Bool \to Unit, x \in Bool, y \in Bool,\; \operatorname{ConceptIdentity}\left(q, x, y\right) \land x \ne y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity.concept_identity_strictly_coarser_than_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal equality is always preserved by every concept readout: equal objects necessarily receive the same concept value.

The containment can be strict. The constant readout from the two Boolean values to the one-point type identifies false and true relative to the concept even though the two source values remain unequal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity.concept_identity_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity.concept_identity_strictly_coarser_than_equality`
