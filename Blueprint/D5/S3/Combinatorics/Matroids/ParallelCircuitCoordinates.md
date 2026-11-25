# Parallel Circuit Coordinates

## Abstract

Circuits of a parallel expansion.

**Theorem 1.1 (Circuits of a parallel expansion).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_circuit_cases`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_circuit_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each vertex projects to a nonloop, a circuit in the pullback is either a pair of distinct vertices in one fiber or an injective lift of a core circuit.

**Theorem 1.2 (Contracted bases under the projection).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_contract_isBase_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_contract_isBase_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a surjective label map and a contraction set contained in the expanded ground, a contracted basis is exactly an injective lift of a core basis after contraction by the image of the set.

**Theorem 1.3 (Projection of a transverse readout).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_on_transversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_on_transversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a block-ordered projection, let two finite faces project injectively with disjoint images. The signed deletion sum over the first face on coefficients projected to the core equals the signed deletion sum of the two image faces.

**Theorem 1.4 (Boundary weighted by fiber size).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.pullbackChain_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.pullbackChain_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a block-ordered projection, take a finite face whose vertices project injectively. The augmented boundary of the pulled-back chain is the sum over insertions outside the image face. Each term has its ordered incidence sign and multiplicity equal to the size of the inserted class.

**Theorem 1.5 (A pair circuit compares two coefficients).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_of_parallel_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_of_parallel_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a block-ordered projection, two distinct vertices with the same label and a transverse face avoiding that label give a signed deletion sum equal to zero exactly when the two single-vertex insertions have equal coefficients.

**Theorem 1.6 (Constancy along fiber exchanges).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.transversal_coeff_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.transversal_coeff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite faces which project injectively to the same face have equal coefficients when single exchanges of representatives over that image preserve the coefficient. The number of vertices outside the destination decreases at each exchange.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_circuit_cases`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.comap_contract_isBase_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.pullbackChain_boundary`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_of_parallel_pair`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.signed_readout_on_transversal`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates.transversal_coeff_eq`
- Dependency: [D5/S3/Combinatorics/Matroids/RationalTopCycleResidues](RationalTopCycleResidues.md)
