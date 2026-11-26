# Circuit Coordinates with One Omitted Basis

## Abstract

The residue equations for a uniform core with one omitted basis.

**Theorem 1.1 (The missing basis imposes one vanishing coordinate).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.mem_weightedCircuitResidues_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.mem_weightedCircuitResidues_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the bases on the full finite ordered ground be the subsets of the given rank except for the omitted set H. A residue chain satisfies the weighted circuit equations exactly when it vanishes off the given rank and on H, its weighted boundary vanishes, and each signed deletion sum on a set of size one greater than the rank vanishes. The circuit H yields one signed row for each singleton basis after contraction. That row agrees up to an overall sign with the deletion row on H joined with the singleton, since the H coordinate vanishes.

**Theorem 1.2 (Alternating forms for the punctured core).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_weighted_forms_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_weighted_forms_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue equations are the uniform alternating-form equations together with vanishing on the omitted basis.

**Theorem 1.3 (The omitted coordinate after pivoting).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_pivot_forms_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_pivot_forms_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the pivot in the omitted basis. The residue module is isomorphic to the forms of one lower degree killed by insertion of the pivot, insertion of the weighted vector, and multiplication by the total size. The coefficient on the omitted basis with the pivot removed must vanish. It agrees with the original omitted coefficient up to its deletion sign.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.mem_weightedCircuitResidues_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_pivot_forms_equiv`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates.punctured_weighted_forms_equiv`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates](UniformMatroidCircuitCoordinates.md)
