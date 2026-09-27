# Original base lattices and full-period geometry

## Abstract

Constructive rectangular transversals identify the exact indices of the six-row and seven-row homogeneous kernels.

**Definition 1.1 (Triangular lattice map).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Lattice.latticeMap`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Lattice.latticeMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive homomorphism maps (u,v) to (A u + C v,D v).

**Definition 1.2 (Six-row homogeneous lattice).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Lattice.sixLattice`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Lattice.sixLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of latticeMap 360 228 24 has basis columns (360,0),(228,24).

**Definition 1.3 (Seven-row homogeneous lattice).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Lattice.sevenLattice`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Lattice.sevenLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of latticeMap 3960 3108 24 has basis columns (3960,0),(3108,24).

**Definition 1.4 (Rectangular quotient representatives).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Lattice.latticeCoset`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Lattice.latticeCoset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q in Fin A times Fin 24, latticeCoset A C is the quotient class of the corresponding integer pair modulo the image of latticeMap A C 24.

**Theorem 1.5 (Kernel geometry).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Lattice.base_lattice_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203Lattice.base_lattice_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The seven-row kernel has basis (3960,0),(3108,24). The six-row and seven-row rectangles are complete transversals with indices 8640 and 95040. Both kernels contain every translate by the original period in either coordinate.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203Lattice.base_lattice_geometry`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Lattice.latticeCoset`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Lattice.latticeMap`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Lattice.sevenLattice`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Lattice.sixLattice`
- Dependency: [D5/S3/Arith/Covering/Erdos203Normalization](Erdos203Normalization.md)
