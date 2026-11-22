# Circuit Coordinates for Sparse Paving Cores

## Abstract

Signed circuit equations for a family of omitted bases.

**Theorem 1.1 (Omitted coefficients and uniform deletion rows).**

Lean statement: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All bases have the stated rank, and the excluded sets of that rank have pairwise intersection at most two below the rank. The weighted residue group comprises the chains supported on the rank-sized subsets that vanish on the excluded sets, have zero weighted boundary, and satisfy every signed deletion row on a subset of size one greater than the rank. At most one excluded set lies in such a subset. Its contraction row replaces the corresponding uniform row up to an overall sign.

**Theorem 1.2 (The alternating-form description).**

Lean statement: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.sparse_paving_weighted_forms_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.sparse_paving_weighted_forms_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a basis on which the covector takes the value one, the uniform deletion rows give covector multiplication and the weighted boundary gives vector insertion. Both operations vanish, and each omitted basis sets the corresponding alternating coefficient to zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.sparse_paving_weighted_forms_equiv`
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates](PuncturedCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitSplit](PuncturedCircuitSplit.md)
