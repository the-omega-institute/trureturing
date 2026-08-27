# Protocol Innovation Criterion

## Abstract

A protocol is innovative exactly when it separates a current observation fiber.

**Theorem 1.1 (Protocol innovation is an explicit fiber separation).**

$$\begin{gathered}\forall X, P, Y: \operatorname{Type},\\{}q: X \to P, L: X \to Y,\\{}\operatorname{ker}\left(\operatorname{conceptJoin}\left(q, L\right)\right) \subset \operatorname{ker}\left(q\right) \iff \\{}\exists x, y: X, q(x) = q(y) \land L(x) \neq L(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion.protocol_innovation_iff_separates_current_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current protocol and the added protocol law are source readouts. Their canonical concept join records both values without introducing a parallel completion object.

The joined kernel is a proper subset of the current kernel exactly when two currently indistinguishable states receive different values from the added protocol law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion.protocol_innovation_iff_separates_current_fiber`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
