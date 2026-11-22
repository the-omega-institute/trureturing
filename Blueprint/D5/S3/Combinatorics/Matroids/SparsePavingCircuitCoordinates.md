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

**Theorem 1.3 (The face coefficient as a form on differences).**

Lean statement: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.wedge_coordinate_zero_iff_differences`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.wedge_coordinate_zero_iff_differences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a basis where the covector takes value one, choose any representative vertex of the face. Subtract it from the other vertices to obtain vectors in the kernel of the covector. The face coefficient of the covector product vanishes exactly when the lower-degree alternating form vanishes on these differences.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.sparse_paving_weighted_forms_equiv`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates.wedge_coordinate_zero_iff_differences`
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates](PuncturedCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitSplit](PuncturedCircuitSplit.md)
