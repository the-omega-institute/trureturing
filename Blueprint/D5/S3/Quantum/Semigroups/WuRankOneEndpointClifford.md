# Pauli eigenvectors of the Wu endpoint

## Abstract

The signed endpoint acts diagonally on two-mode Pauli words.

The sign in the entrywise formula makes the exponent depend on the Clifford degree of a word. The sixteen eigenvalue identities follow from the entry formula and the fixed Pauli matrix convention.

**Theorem 1.1 (Pauli eigenvalue formula).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.A1_pauliWord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.A1_pauliWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each two-mode Pauli word of Clifford degree d is an eigenvector of the actual signed map with eigenvalue λᵈ.

**Definition 1.2 (The degree of a Pauli word).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.cliffordDegree`

*Formalization.* `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.cliffordDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree records the exponent for each of the sixteen Pauli words.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.A1_pauliWord`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.cliffordDegree`
- Dependency: [D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor](WuRankOneEndpointFloor.md)
