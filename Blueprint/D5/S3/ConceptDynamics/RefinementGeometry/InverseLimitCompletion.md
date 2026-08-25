# Inverse Limit Completion

## Abstract

A refinement tower matches states to its threads iff separating and complete.

**Theorem 1.1 (States correspond bijectively to threads exactly under completeness and separation).**

$$\operatorname{Bijective}\left(\operatorname{stateThread}\left(system\right)\right) \iff (\operatorname{ThreadComplete}\left(system\right) \land \operatorname{SeparatesStates}\left(system\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

stateThread maps each state to its compatible values at every refinement stage. ThreadComplete is its surjectivity and SeparatesStates is all-stage injectivity.

The injectivity criterion paired with thread completeness gives the bijection biconditional.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
