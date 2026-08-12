# Standard-Basis Qubit Pinching

## Abstract

Standard-basis qubit pinching is an idempotent Hilbert-Schmidt projection with exact forcing tests.

**Definition 1.1 (Standard-basis pinching is zero-retention phase damping).**

Lean statement: `D5/S3/QuantumChannels/Pinching.pinching`

*Formalization.* `D5/S3/QuantumChannels/Pinching.pinching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex two-by-two matrix rho, pinching is exactly the existing phaseDamping map at coherence-retention coefficient zero. Thus diagonal entries are preserved and all off-diagonal entries are annihilated. No parallel channel definition, positivity premise, Hermiticity premise, or trace-one premise is introduced.

**Definition 1.2 (The Hilbert-Schmidt pairing is the trace pairing).**

Lean statement: `D5/S3/QuantumChannels/Pinching.hilbertSchmidtInner`

*Formalization.* `D5/S3/QuantumChannels/Pinching.hilbertSchmidtInner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For qubit matrices A and B, the scalar pairing is trace of the conjugate transpose of A times B. Mathlib supplies matrix trace and conjugate transpose, but its Frobenius matrix scope does not install an Inner instance for Matrix, so this declaration is the minimal formula-level wrapper rather than a competing inner-product-space structure.

**Theorem 1.3 (Pinching is idempotent).**

$$P \circ P=P$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/Pinching.pinching_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying standard-basis pinching twice is the same function as applying it once. The equality is extensional over every complex two-by-two input and every matrix entry.

**Theorem 1.4 (Pinching is Hilbert-Schmidt self-adjoint).**

$$\forall A,B \in M_{2}(\mathbb{C}),\ \langle P(A), B\rangle_{HS}=\langle A, P(B)\rangle_{HS}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/Pinching.pinching_hilbert_schmidt_self_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert-Schmidt pairing is unchanged when pinching is moved from the first argument to the second. Entrywise expansion leaves exactly the two diagonal contributions on both sides, proving the full scalar equality rather than only equality of real parts, norms, or zero sets.

**Theorem 1.5 (Zero entries force complete off-diagonal elimination).**

$$\forall \rho,i,j,\ (P(\rho))_{ij}=0 \Leftrightarrow i\neq j \lor \rho_{ij}=0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/Pinching.pinching_entry_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every matrix and every pair of standard-basis indices, a pinched entry is zero exactly when it is off diagonal or the original entry was already zero. A weakened map retaining any nonzero multiple of a nonzero off-diagonal entry cannot satisfy this equivalence.

**Theorem 1.6 (Pinching annihilates the purely off-diagonal Pauli X).**

$$\langle P(X), X\rangle_{HS}=0 \land \langle X, X\rangle_{HS}\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/Pinching.pinching_annihilates_offdiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pauli X matrix is purely off diagonal, so pinching sends it to zero while its own Hilbert-Schmidt norm stays nonzero. Any map that merely attenuates coherence, retaining a nonzero multiple of the off-diagonal weight, falsifies the first conjunct, so this pair separates pinching from every partial damping channel.

## References

- Truth anchor: `D5/S3/QuantumChannels/Pinching.hilbertSchmidtInner`
- Truth anchor: `D5/S3/QuantumChannels/Pinching.pinching`
- Truth anchor: `D5/S3/QuantumChannels/Pinching.pinching_annihilates_offdiagonal`
- Truth anchor: `D5/S3/QuantumChannels/Pinching.pinching_entry_eq_zero_iff`
- Truth anchor: `D5/S3/QuantumChannels/Pinching.pinching_hilbert_schmidt_self_adjoint`
- Truth anchor: `D5/S3/QuantumChannels/Pinching.pinching_idempotent`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../Quantum/QubitWitnesses.md)
