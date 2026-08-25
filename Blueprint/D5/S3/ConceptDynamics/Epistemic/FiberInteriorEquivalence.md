# Fiber Interior Equivalence

## Abstract

Interior truth in a readout partition topology is exactly truth on the current readout fiber.

**Theorem 1.1 (Fiber knowledge equivalence).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}C: Concept(X, B), P: Set(X),\\{}x: X,\\{}x \in interior(partitionTopology(C), P) \iff \forall y: X, C(y) = C(x) \Rightarrow y \in P.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence.fiber_interior_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The topology is the canonical partition topology induced by the readout into a discrete coordinate space.

An interior set is open and therefore saturated along readout fibers. Membership at x consequently transfers to every y with the same readout before factivity gives membership in P.

Conversely, the readout fiber through x is open in the partition topology. If P holds throughout that fiber, the fiber is an open neighborhood of x contained in P, so x lies in the interior.

The module imports the existing partition topology and fiber knowledge primitives; repository and pinned-library searches found no exact theorem for their equivalence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/FiberInteriorEquivalence.fiber_interior_equivalence`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection](PartitionKnowledgeNegativeIntrospection.md)
