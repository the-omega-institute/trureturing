# Difference Coordinates around Two Representatives

## Abstract

Integral difference coordinates with a representative inside a block.

**Theorem 1.1 (Difference vectors in a block and its complement).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a global representative outside the block and a local representative inside. A vector at another index in the block becomes its difference from the local representative. Every other non-global index uses its difference from the global representative. The two corresponding coordinates of a vector are its block sum and its total sum.

**Theorem 1.2 (Simultaneous coordinates for the two face differences).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_two_face_difference_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_two_face_difference_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both faces have a common vertex, choose it as their representative. For disjoint faces, choose separate representatives and sum the weights in the second face into its representative's coordinate. In either case the difference tuples occur together in an integral basis, the transformed weights stay positive, and the first tuple has at least two indices outside the second.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_difference_basis`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis.exists_two_face_difference_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitBasis](UniformCircuitBasis.md)
