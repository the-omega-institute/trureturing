# Reduced Omitted-Triangle Coordinates

## Abstract

Reduced matrix coordinates for the integral rank-three lifting obstruction.

**Theorem 1.1 (Reduced matrix for the integral obstruction).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates.rank_three_lifting_obstruction_equiv_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates.rank_three_lifting_obstruction_equiv_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the bases on a finite ordered ground set of size n greater than three are all triples except a specified family whose distinct members meet in at most one point. For singleton parallel classes and any distinct root and anchor, the integral lifting obstruction is linearly equivalent over the integers to the kernel of the reduced omitted-triangle matrix modulo n. Each column is an increasing pair avoiding the root and anchor. The row of a triple evaluates the alternating form on two differences from the first point of the triple.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates.rank_three_lifting_obstruction_equiv_kernel`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis](CircuitDifferenceBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations](RankThreeOmissionRelations.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal](UniformCircuitResidueDiagonal.md)
