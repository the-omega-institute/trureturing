# Difference Coordinates around Two Representatives

## Abstract

Integral difference coordinates with a representative inside a block.

**Theorem 1.1 (Difference vectors in a block and its complement).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a global representative outside the block and a local representative inside. A vector at another index in the block becomes its difference from the local representative. Every other non-global index uses its difference from the global representative. The two corresponding coordinates of a vector are its block sum and its total sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitBasis](UniformCircuitBasis.md)
