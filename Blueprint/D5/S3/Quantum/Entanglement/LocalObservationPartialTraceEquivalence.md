# Local Observation Partial-Trace Equivalence

## Abstract

Complete local effects distinguish exactly the reduced density state.

**Theorem 1.1 (Local observation equivalence is reduced-state equality).**

$$\forall A \in Type, B \in Type, rho \in DensityState\left(A \times B\right), sigma \in DensityState\left(A \times B\right),\; Fintype\left(A\right) \land DecidableEq\left(A\right) \land Fintype\left(B\right) \land DecidableEq\left(B\right) \Rightarrow \left(\left(\forall E \in Matrix\left(B, B, \mathbb{C}\right),\; Hermitian\left(E\right) \Rightarrow Tr\left(partialTraceFirst\left(\rho\right) E\right) = Tr\left(partialTraceFirst\left(sigma\right) E\right)\right) \Leftrightarrow partialTraceFirst\left(\rho\right) = partialTraceFirst\left(sigma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.local_observation_partial_trace_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The states are finite bipartite density matrices. The first-factor partial trace is constructed by summing entries with equal first indices.

Equality of trace pairings against every Hermitian second-factor effect is equivalent to equality of the two reduced matrices.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.local_observation_partial_trace_equivalence`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
