# Dao Concept Boundary Specialization

## Abstract

A set-theoretic specialization makes precise how a concept, its relative opposite, and the ambient horizon delimit one another.

The horizon is an explicitly chosen set, a concept is a subset, and its opposite is the relative difference of the horizon by that concept. This is a conditional mathematical model of non-exhaustive naming. It does not identify the historical Dao with a set, prove that every expression has a set-valued meaning, or establish the metaphysical premise that every expression leaves a nonempty remainder.

**Theorem 1.1 (A concept boundary is exactly a nonempty remainder).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right), C \in \operatorname{Set}\left(X\right),\; \left(C \subseteq H \land C \ne H\right) \Leftrightarrow \left(C \subseteq H \land \operatorname{Nonempty}\left(\operatorname{sdiff}\left(H, C\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.concept_boundary_iff_nonempty_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept is a proper subset of its horizon exactly when it lies inside that horizon and leaves at least one point of the horizon outside the concept.

**Theorem 1.2 (The relative opposite is proper exactly when the concept is present).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right), C \in \operatorname{Set}\left(X\right),\; \left(\operatorname{sdiff}\left(H, C\right) \subseteq H \land \operatorname{sdiff}\left(H, C\right) \ne H\right) \Leftrightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(H, C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.relative_opposite_is_proper_iff_concept_present` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the concept from the horizon leaves a proper part precisely when the concept contains a point that also lies in the horizon.

**Theorem 1.3 (Concept and relative opposite recover the horizon).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right), C \in \operatorname{Set}\left(X\right),\; C \subseteq H \Rightarrow \operatorname{union}\left(\operatorname{sdiff}\left(H, C\right), C\right) = H$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.relative_opposite_and_concept_cover_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever the concept lies inside the horizon, the union of the concept and its relative opposite is exactly the horizon.

**Theorem 1.4 (Relative opposites distinguish concepts in one horizon).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right), C \in \operatorname{Set}\left(X\right), D \in \operatorname{Set}\left(X\right),\; \left(C \subseteq H \land D \subseteq H\right) \Rightarrow \left(\operatorname{sdiff}\left(H, C\right) = \operatorname{sdiff}\left(H, D\right) \Leftrightarrow C = D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.equal_relative_opposites_iff_equal_concepts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two concepts contained in the same horizon, their relative opposites are equal exactly when the concepts are equal.

**Theorem 1.5 (Every non-exhaustive expression denotes a proper part).**

$$\forall X \in Type, E \in Type, H \in \operatorname{Set}\left(X\right), m \in E \to \operatorname{Set}\left(X\right),\; \left(\left(\forall e \in E,\; m\left(e\right) \subseteq H\right) \land \left(\forall e \in E,\; \operatorname{Nonempty}\left(\operatorname{sdiff}\left(H, m\left(e\right)\right)\right)\right)\right) \Rightarrow \left(\forall e \in E,\; m\left(e\right) \subseteq H \land m\left(e\right) \ne H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.admissible_expressions_are_proper_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each expression denotes something inside the horizon and leaves a nonempty relative remainder, then every such denotation is a proper part of the horizon.

**Theorem 1.6 (The name Dao obeys the same conditional boundary).**

$$\forall X \in Type, E \in Type, H \in \operatorname{Set}\left(X\right), m \in E \to \operatorname{Set}\left(X\right), d \in E,\; \left(\left(\forall e \in E,\; m\left(e\right) \subseteq H\right) \land \left(\forall e \in E,\; \operatorname{Nonempty}\left(\operatorname{sdiff}\left(H, m\left(e\right)\right)\right)\right)\right) \Rightarrow \left(m\left(d\right) \subseteq H \land m\left(d\right) \ne H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.dao_name_is_a_proper_part_under_the_same_premises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A distinguished expression token called Dao is no exception: under the same universal containment and remainder premises, its denotation is a proper part of the horizon.

**Theorem 1.7 (An empty concept has the whole horizon as its opposite).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right),\; \operatorname{sdiff}\left(H, \left\{\right\}\right) = H$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.empty_concept_opposite_is_whole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty-concept boundary case shows why concept presence is necessary: its relative opposite is the entire horizon.

**Theorem 1.8 (The whole horizon leaves no relative remainder).**

$$\forall X \in Type, H \in \operatorname{Set}\left(X\right),\; \operatorname{sdiff}\left(H, H\right) = \left\{\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.whole_horizon_leaves_no_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the other boundary, taking the entire horizon as the concept leaves the empty relative remainder.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.admissible_expressions_are_proper_parts`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.concept_boundary_iff_nonempty_remainder`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.dao_name_is_a_proper_part_under_the_same_premises`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.empty_concept_opposite_is_whole`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.equal_relative_opposites_iff_equal_concepts`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.relative_opposite_and_concept_cover_horizon`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.relative_opposite_is_proper_iff_concept_present`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.whole_horizon_leaves_no_remainder`
- Dependency: [D5/S3/ConceptDynamics/Negation/RelativeComplement](RelativeComplement.md)
