# Relational Weakest-Precondition Composition

## Abstract

Universal weakest preconditions compose in reverse process order.

**Theorem 1.1 (Weakest preconditions propagate backward through a composite).**

$$\forall X \in Type, Y \in Type, Z \in Type, R \in \operatorname{SetRel}\left(X, Y\right), S \in \operatorname{SetRel}\left(Y, Z\right), Q \in \operatorname{Set}\left(Z\right),\; \operatorname{universalWeakestPrecondition}\left(\operatorname{SetRelComp}\left(R, S\right), Q\right) = \operatorname{universalWeakestPrecondition}\left(R, \operatorname{universalWeakestPrecondition}\left(S, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/RelationalWeakestPreconditionComposition.universal_weakest_precondition_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two relations have the source, intermediate, and final carriers shown in the formula. The predicate transformer is the canonical relational core, and the proof applies the pinned library composition law directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/RelationalWeakestPreconditionComposition.universal_weakest_precondition_composition`
- Dependency: [D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction](RelationalPreconditionAdjunction.md)
