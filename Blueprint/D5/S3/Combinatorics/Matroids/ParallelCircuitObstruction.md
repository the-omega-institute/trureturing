# Parallel Circuit Obstruction

## Abstract

The rational residue correspondence.

**Theorem 1.1 (The rational residue correspondence).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_rational_residue_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_rational_residue_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a surjective block-ordered projection whose vertices map to nonloops, quotient the rational top cycles with integral joint readouts by the integral cycles. The quotient is linearly equivalent over the integers to residue chains on the core with zero weighted boundary and zero circuit readouts. On each face the pullback of the image chain equals the residue of the original coefficient.

**Theorem 1.2 (The weighted lifting obstruction).**

Lean statement: `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_lifting_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_lifting_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty expanded ground with a surjective block-ordered projection to nonloops of a finite ordered matroid, the saturation of the integral joint restriction image modulo the image is linearly equivalent over the integers to the residue chains on core bases satisfying both families of equations. Boundary insertions carry their fiber sizes. Circuit readouts use the ordinary signed deletion and shuffle signs. When a saturated readout is represented by a rational top cycle, pulling its image chain back along the projection recovers the residue of that cycle in every face coordinate.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_lifting_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction.parallel_rational_residue_comparison`
- Dependency: [D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates](ParallelCircuitCoordinates.md)
