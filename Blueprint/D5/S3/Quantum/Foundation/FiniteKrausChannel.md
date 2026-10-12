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

**Theorem 1.2 (Kronecker amplification distributes over addition).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, C \in \operatorname{Type}, D \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{Fintype}\left(C\right)] [\operatorname{Fintype}\left(D\right)] [\operatorname{DecidableEq}\left(C\right)] [\operatorname{CommSemiring}\left(R\right)] \forall ML1 \in \operatorname{MatrixMap}\left(A, B, R\right), ML2 \in \operatorname{MatrixMap}\left(A, B, R\right), MR \in \operatorname{MatrixMap}\left(C, D, R\right),\; \operatorname{MatrixMap}.\operatorname{kron}\left(ML1 + ML2, MR\right) = \operatorname{MatrixMap}.\operatorname{kron}\left(ML1, MR\right) + \operatorname{MatrixMap}.\operatorname{kron}\left(ML2, MR\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MatrixMap.kron is additive in its first matrix map over a commutative semiring. The finite coordinate types A, B, C and D may be empty. This identity gives the addition closure of MatrixMap.IsCompletelyPositive.

**Theorem 1.3 (Completely positive maps are closed under addition).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{RCLike}\left(R\right)] \forall M1 \in \operatorname{MatrixMap}\left(A, B, R\right), M2 \in \operatorname{MatrixMap}\left(A, B, R\right),\; \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M1\right) \Rightarrow \left(\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M2\right) \Rightarrow \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M1 + M2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite A and B and an RCLike scalar R, the sum of two completely positive matrix maps is completely positive. At every finite amplification, add_kron expresses the image as the sum of two positive semidefinite images. IptPptSquaredEquivalence.gamma_cp uses this closure to combine the four branches of the flag lift.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.add`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
