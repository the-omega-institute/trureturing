# Strongest and Weakest Condition Adjunction

## Abstract

Strongest postconditions and weakest preconditions form the direct-image / inverse-image adjunction.

**Theorem 1.1 (Strongest postconditions are left adjoint to weakest preconditions).**

$$\forall X, Y: \operatorname{Type},\\F: X \to Y, P \subseteq X, Q \subseteq Y,\\\operatorname{sp}_{F}(P) \subseteq Q \iff P \subseteq \operatorname{wp}_{F}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction.sp_wp_adjunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a process F, the strongest postcondition sp_F(P) is the direct image of P. The weakest precondition wp_F(Q) is the inverse image defined by the preceding frozen module.

The displayed equivalence quantifies over arbitrary state types, a process, a source predicate P, and a target predicate Q. It states both directions of the image-preimage inclusion adjunction.

Pinned Mathlib's Set.image_preimage packages exactly this Galois connection, with Set.image_subset_iff as its defining theorem. The proof only specializes that result and unfolds the two condition definitions. Repository searches found no existing D5 theorem packaging the program-logic vocabulary.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction.sp_wp_adjunction`
- Dependency: [D5/S3/ObserverMemory/Knowledge/WeakestPrecondition](WeakestPrecondition.md)
