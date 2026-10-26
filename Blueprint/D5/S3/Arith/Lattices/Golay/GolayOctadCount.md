# Second moments and Golay octads

## Abstract

Second moments and Golay octads

Pair projections and the second Hamming-weight moment determine the octad count without a list of code messages. The parameterized argument varies the binary linear code. Fiber counting and moment identities are classical methods; no originality claim is made.

**Theorem 1.1 (Octads from structural hypotheses).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any binary linear subspace C on twenty-four coordinates, assume cardinality 4096, membership of the all-ones word, equality to its coordinate-pairing orthogonal, minimum nonzero weight at least eight, and weight spectrum contained in zero, eight, twelve, sixteen and twenty-four. The subtype of weight-eight words then has cardinality 759. Self-duality and minimum weight force every two-coordinate projection to be surjective. Its four fibers each have 1024 elements, giving second moment 565248. Complementation equates the weight-eight and weight-sixteen counts. The size and moment equations force 759.

**Theorem 1.2 (Octads of the actual polynomial code).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card` (`✓ std3`). ∎

*Citation.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Commentary.*

The weight-eight subtype of the original polynomial encoder image has cardinality 759. The established code cardinality, all-ones membership, self-duality, minimum weight and weight spectrum supply every hypothesis of the structural theorem. This is the classical Golay octad count.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayOctadCount.octad_count_of_self_dual`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayEncoder](GolayEncoder.md)
