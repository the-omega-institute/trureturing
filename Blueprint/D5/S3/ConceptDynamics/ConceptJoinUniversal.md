# Concept Join Universal Property

## Abstract

The product readout is the universal join of two concept readouts.

**Definition 1.1 (Refinement is factorization through the finer readout).**

$$\forall X, C, D: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D,\\{}\operatorname{Refines}\left(q_{C}, q_{D}\right) \iff \exists factor: D \to C, q_{C} = factor \circ q_{D}.$$

*Formalization.* `D5/S3/ConceptDynamics/ConceptJoinUniversal.Refines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For readouts q_C : X -> C and q_D : X -> D, q_C is refined by q_D exactly when a map from D to C recovers q_C after q_D. The equality is an equality of functions, not merely pointwise implication.

**Theorem 1.2 (The product readout is the universal join).**

$$\forall X, C, D, E: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D, q_{E}: X \to E,\ \operatorname{Refines}\left(q_{C}, \operatorname{conceptJoin}\left(q_{C}, q_{D}\right)\right) \land \operatorname{Refines}\left(q_{D}, \operatorname{conceptJoin}\left(q_{C}, q_{D}\right)\right) \land \operatorname{Refines}\left(q_{C}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(q_{D}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{C}, q_{D}\right), q_{E}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ConceptJoinUniversal.concept_join_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint readout sends x to the pair (q_C x, q_D x). The first two conjuncts factor the component readouts through the product projections.

If both component readouts factor through q_E, pairing their factor maps gives the factor map from q_E to the joint readout. This is the universal property of the concept join.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ConceptJoinUniversal.Refines`
- Truth anchor: `D5/S3/ConceptDynamics/ConceptJoinUniversal.concept_join_universal`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](ConceptFiberDecomposition.md)
