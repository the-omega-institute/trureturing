# Relational Strongest-Postcondition Composition

## Abstract

Relational strongest postconditions compose in forward process order.

**Theorem 1.1 (Strongest postconditions follow the process order).**

$$\forall X \in Type, Y \in Type, Z \in Type, R \in \operatorname{SetRel}\left(X, Y\right), S \in \operatorname{SetRel}\left(Y, Z\right),\; \operatorname{relationalStrongestPostcondition}\left(\operatorname{SetRelComp}\left(R, S\right)\right) = \operatorname{compose}\left(\operatorname{relationalStrongestPostcondition}\left(S\right), \operatorname{relationalStrongestPostcondition}\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/RelationalStrongestPostconditionComposition.relational_strongest_postcondition_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality is between set transformers. Relational composition first applies R and then S, while relational image first propagates through R and then through S; the proof is the pinned library image law.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/RelationalStrongestPostconditionComposition.relational_strongest_postcondition_composition`
- Dependency: [D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction](RelationalPreconditionAdjunction.md)
