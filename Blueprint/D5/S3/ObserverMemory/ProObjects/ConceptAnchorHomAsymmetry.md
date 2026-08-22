# Constant-Object Hom Formulas for Presented Pro-Objects

## Abstract

Constant-object morphisms in a presented pro-object compute as a stage colimit and a stage limit.

**Theorem 1.1 (The two constant-object Hom formulas).**

$$\forall C, J, X: J^{op} \to C, A, D: C, \operatorname{Hom}_{\operatorname{Pro}(C)}(X, c(D)) \equiv \operatorname{colim}_{j} \operatorname{Hom}_{C}(X_{j}, D) \land \operatorname{Hom}_{\operatorname{Pro}(C)}(c(A), X) \equiv \operatorname{lim}_{j} \operatorname{Hom}_{C}(A, X_{j}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry.concept_anchor_hom_asymmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a small filtered category and let X : J^op -> C be the cofiltered stage diagram. The presented pro-object is constructed as the opposite of the Ind-colimit of the opposite diagram, while cA and cD are constructed by the opposite Ind-Yoneda embedding.

A morphism from X to cD is canonically equivalent to the filtered colimit of the stage morphisms X_j -> D. In the reverse direction, a morphism from cA to X is canonically equivalent to the cofiltered limit of the stage morphisms A -> X_j.

The Lean construction applies the pinned fully faithful Ind inclusion, its limit-to-inclusion comparison, Yoneda, pointwise colimit preservation, and the library Hom-limit equivalence directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry.concept_anchor_hom_asymmetry`
