# Slater prefix contraction with diagonal compression

## Abstract

Slater prefix contraction with diagonal compression

**Definition 1.1 (Stack the retained and discarded rows).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackRows`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List the rows of the retained matrix first and then the rows of the discarded matrix.

**Definition 1.2 (Determinant rows at fixed occupation).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stack the supplied retained rows above the increasing enumeration of the selected discarded rows. The retained row count plus the discarded occupation count is the column count.

**Theorem 1.3 (Reindex a selected retained minor).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor_cast_selected`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor_cast_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality of the occupied size and the row size lets either proof of the same column count be used to form the minor.

**Definition 1.4 (Determinant amplitude matrix of a prefix).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.prefixAmplitudes`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.prefixAmplitudes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Index rows and columns by the full retained and discarded occupation sets. A coefficient is the ordered occupied minor if the total occupation equals the particle count, and zero otherwise.

**Theorem 1.5 (Product weights for diagonal retained compression).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.diagonal_prefixMarginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.diagonal_prefixMarginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rectangular complex matrices P and Y with the same column space index, assume P adjoint P plus Y adjoint Y is the identity. If P times P adjoint is diagonal with entries nu, the Gram matrix of the determinant amplitudes is diagonal over all retained occupation subsets. Its weight is the product of nu on occupied labels and one minus nu on unoccupied labels. The proof extracts the relevant weighted determinant coefficients using Cauchy–Binet.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.diagonal_prefixMarginal`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.prefixAmplitudes`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackMinor_cast_selected`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterPrefixContraction.stackRows`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
