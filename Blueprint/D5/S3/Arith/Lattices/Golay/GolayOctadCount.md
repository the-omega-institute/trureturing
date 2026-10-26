# Second moments and Golay octads

## Abstract

Second moments and Golay octads

Pair projections and the second Hamming-weight moment determine the octad count without a list of code messages. The parameterized argument varies the binary linear code. Fiber counting and moment identities are classical methods; no originality claim is made.

**Definition 1.1 (Two-coordinate additive projection).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection`

*Formalization.* `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a binary linear subspace C and coordinates i and j, pairProjection is the additive map sending a codeword c to its actual coordinate pair (c_i,c_j).

**Theorem 1.2 (Surjectivity at distinct coordinates).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any binary linear subspace C containing the all-ones word, equal to its coordinate-pairing orthogonal, and having minimum nonzero weight at least eight, the actual projection to any two distinct coordinates is surjective onto F2 times F2. Failure to separate the coordinates would put their weight-two indicator in C, contradicting the minimum-weight assumption. This exposed original helper supplies the Leech axis distribution.

**Theorem 1.3 (Size of the two-one fiber).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pair_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pair_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same structural hypotheses and cardinality 4096, exactly 1024 codewords have value one at both distinct coordinates. Translation identifies all four fibers. The axis distribution consumes this original fiber count and projection surjectivity to count every bit pair.

**Theorem 1.4 (Octads from structural hypotheses).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any binary linear subspace C on twenty-four coordinates, assume cardinality 4096, membership of the all-ones word, equality to its coordinate-pairing orthogonal, minimum nonzero weight at least eight, and weight spectrum contained in zero, eight, twelve, sixteen and twenty-four. The subtype of weight-eight words then has cardinality 759. Self-duality and minimum weight force every two-coordinate projection to be surjective. Its four fibers each have 1024 elements, giving second moment 565248. Complementation equates the weight-eight and weight-sixteen counts. The size and moment equations force 759.

**Theorem 1.5 (Octads of the actual polynomial code).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card` (`✓ std3`). ∎

*Citation.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Commentary.*

The weight-eight subtype of the original polynomial encoder image has cardinality 759. The established code cardinality, all-ones membership, self-duality, minimum weight and weight spectrum supply every hypothesis of the structural theorem. This is the classical Golay octad count.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pairProjection_surjective`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.pair_fiber_card`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayEncoder](GolayEncoder.md)
