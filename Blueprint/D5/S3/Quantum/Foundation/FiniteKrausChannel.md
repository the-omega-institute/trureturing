# Finite Kraus Quantum Channels

## Abstract

Finite Kraus realizations in the canonical completely positive channel interface.

**Theorem 1.1 (Kraus completeness gives a canonical quantum channel).**

$$\forall A \in FiniteType, B \in FiniteType, R \in FiniteType, K \in R \to \operatorname{Matrix}\left(B, A, \mathbb{C}\right),\; \sum_{r \in R} K\left(r\right)^{*} \cdot K\left(r\right) = 1 \Rightarrow \left(\exists C \in \operatorname{QuantumChannel}\left(A, B\right),\; \forall rho \in \operatorname{Matrix}\left(A, A, \mathbb{C}\right),\; \operatorname{fromCstar}\left(\operatorname{apply}\left(C, \operatorname{toCstar}\left(rho\right)\right)\right) = \sum_{r \in R} K\left(r\right) \cdot rho \cdot K\left(r\right)^{*}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A, B and R are arbitrary finite coordinate types, including empty types. K(r) is a complex matrix from A to B. The sole matrix hypothesis is the displayed completeness identity.

QuantumChannel is the canonical FiniteStateChannel bundle: a Mathlib CompletelyPositiveMap on CStarMatrix, positive at every finite amplification, together with trace preservation for every matrix. The functions toCstar and fromCstar are CStarMatrix.ofMatrix and its inverse. Adjoint means conjugate transpose. The displayed action holds for every input matrix.

The private proof closure retains Alex Meiburg's Physlib Kraus complete positivity and trace preservation proofs from revision 6a09b2d1761a0d4430083045a247eb121d8da260, under the full Apache 2.0 license retained in the Lean source. A star algebra coordinate equivalence transports its Kronecker amplification to canonical CStarMatrix amplification. The retained closure retires when equivalent declarations enter pinned Mathlib. The concrete shifted-record realization consumes this bridge.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
