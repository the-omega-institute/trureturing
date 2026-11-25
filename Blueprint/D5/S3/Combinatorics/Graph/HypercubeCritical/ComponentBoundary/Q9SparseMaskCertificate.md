# Finite sparse mask certificate

## Abstract

Finite sparse mask certificate

**Definition 1.1 (Bit-vector characteristic support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.support`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer mask records membership of the 512 vertices in the cube.

**Definition 1.2 (Finite row and column contact checks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.sparseMaskCheck`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.sparseMaskCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row test counts masked directions reaching paired fibres at an occupied projected row. The column test counts occupied projected neighbors of each paired fibre.

**Theorem 1.3 (Certified exclusion of universal weighted sharpness).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.not_universal_of_sparseMaskCheck`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.not_universal_of_sparseMaskCheck` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bit-vector coordinate moves transport the two finite inequalities to the sparse Gram criterion for either retained parity and any coherent switching.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.not_universal_of_sparseMaskCheck`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.sparseMaskCheck`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate.support`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram](Q9SparseOccupiedGram.md)
