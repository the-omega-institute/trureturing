# Concept Join Universal Property

## Abstract

The product readout is the universal join of two concept readouts.

**Theorem 1.1 (The product readout is the universal join).**

$$\forall X, C, D, E: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D, q_{E}: X \to E,\ \operatorname{Refines}\left(q_{C}, \operatorname{conceptJoin}\left(q_{C}, q_{D}\right)\right) \land \operatorname{Refines}\left(q_{D}, \operatorname{conceptJoin}\left(q_{C}, q_{D}\right)\right) \land \operatorname{Refines}\left(q_{C}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(q_{D}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{C}, q_{D}\right), q_{E}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ConceptJoinUniversal.concept_join_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint readout sends x to the pair (q_C x, q_D x). The first two conjuncts factor the component readouts through the product projections.

If both component readouts factor through q_E, pairing their factor maps gives the factor map from q_E to the joint readout. This is the universal property of the concept join.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ConceptJoinUniversal.concept_join_universal`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](ConceptFiberDecomposition.md)
