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

The proof closure retains Alex Meiburg's Physlib Kraus complete positivity and trace preservation proofs from revision 6a09b2d1761a0d4430083045a247eb121d8da260, under the full Apache 2.0 license retained in the Lean source. A star algebra coordinate equivalence transports its Kronecker amplification to canonical CStarMatrix amplification. The retained closure retires when equivalent declarations enter pinned Mathlib. The concrete shifted-record realization consumes this bridge.

**Definition 1.2 (Trace preservation on every matrix).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{Semiring}\left(R\right)] \forall M \in \operatorname{MatrixMap}\left(A, B, R\right),\; \operatorname{MatrixMap}.\operatorname{IsTracePreserving}\left(M\right) \Leftrightarrow \left(\forall x \in \operatorname{Matrix}\left(A, A, R\right),\; \operatorname{trace}\left(M\left(x\right)\right) = \operatorname{trace}\left(x\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausChannel.IsTracePreserving` (`✓ std3`).

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

A matrix map is trace preserving when its output has the same trace as its input for every matrix over the semiring.

**Theorem 1.3 (Kraus completeness gives trace preservation).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, S \in \operatorname{Type}, Kappa \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{Fintype}\left(Kappa\right)] [\operatorname{CommSemiring}\left(S\right)] [\operatorname{Star}\left(S\right)] \forall M \in Kappa \to \operatorname{Matrix}\left(B, A, S\right), N \in Kappa \to \operatorname{Matrix}\left(B, A, S\right),\; \sum_{k\in Kappa} \operatorname{conjTranspose}\left(N\left(k\right)\right) \cdot M\left(k\right) = 1 \Rightarrow \operatorname{MatrixMap}.\operatorname{IsTracePreserving}\left(\operatorname{MatrixMap}.\operatorname{of}_{\operatorname{kraus}}\left(M, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus_isTracePreserving` (`✓ std3`). ∎

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Over a commutative semiring with a star operation, the completeness identity for two finite Kraus families makes their matrix map preserve the trace of every input.

**Theorem 1.4 (Kronecker amplification distributes over addition).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, C \in \operatorname{Type}, D \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{Fintype}\left(C\right)] [\operatorname{Fintype}\left(D\right)] [\operatorname{DecidableEq}\left(C\right)] [\operatorname{CommSemiring}\left(R\right)] \forall ML1 \in \operatorname{MatrixMap}\left(A, B, R\right), ML2 \in \operatorname{MatrixMap}\left(A, B, R\right), MR \in \operatorname{MatrixMap}\left(C, D, R\right),\; \operatorname{MatrixMap}.\operatorname{kron}\left(ML1 + ML2, MR\right) = \operatorname{MatrixMap}.\operatorname{kron}\left(ML1, MR\right) + \operatorname{MatrixMap}.\operatorname{kron}\left(ML2, MR\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MatrixMap.kron is additive in its first matrix map over a commutative semiring. The finite coordinate types A, B, C and D may be empty. This identity gives the addition closure of MatrixMap.IsCompletelyPositive.

**Theorem 1.5 (Completely positive maps are closed under addition).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{RCLike}\left(R\right)] \forall M1 \in \operatorname{MatrixMap}\left(A, B, R\right), M2 \in \operatorname{MatrixMap}\left(A, B, R\right),\; \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M1\right) \Rightarrow \left(\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M2\right) \Rightarrow \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(M1 + M2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite A and B and an RCLike scalar R, the sum of two completely positive matrix maps is completely positive. At every finite amplification, add_kron expresses the image as the sum of two positive semidefinite images. IptPptSquaredEquivalence.gamma_cp uses this closure to combine the four branches of the flag lift.

**Definition 1.6 (Conjugation as a linear matrix map).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{RCLike}\left(R\right)] \forall y \in \operatorname{Matrix}\left(B, A, R\right), x \in \operatorname{Matrix}\left(A, A, R\right),\; \operatorname{MatrixMap}.\operatorname{conj}\left(y\right)\left(x\right) = y \cdot x \cdot \operatorname{conjTranspose}\left(y\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausChannel.conj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite input coordinate type A and an RCLike scalar R, MatrixMap.conj y is the linear map sending x to y x y adjoint, with arbitrary output coordinate type B.

**Theorem 1.7 (Evaluation of matrix conjugation).**

$$\forall A \in \operatorname{Type}, B \in \operatorname{Type}, R \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{RCLike}\left(R\right)] \forall y \in \operatorname{Matrix}\left(B, A, R\right), x \in \operatorname{Matrix}\left(A, A, R\right),\; \operatorname{MatrixMap}.\operatorname{conj}\left(y\right)\left(x\right) = y \cdot x \cdot \operatorname{conjTranspose}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausChannel.conj_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating MatrixMap.conj y at x gives y x y adjoint for every matrix x on the finite input coordinate type.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.IsTracePreserving`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.add`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.conj`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.conj_apply`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus_isTracePreserving`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
