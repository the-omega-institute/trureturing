# Refinement Transitivity

## Abstract

Refinement witnesses compose through the intermediate readout carrier.

**Theorem 1.1 (Refinement witnesses compose).**

$$\operatorname{Refines}(q1, q2) \Rightarrow \operatorname{Refines}(q, q1) \Rightarrow \operatorname{Refines}(q, q2).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/RefinementTransitivity.refinement_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical refinement relation is factorization through a forgetting map.

Composing the two source factorization witnesses produces the factor from the finest readout directly to the coarsest.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/RefinementTransitivity.refinement_transitive`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
