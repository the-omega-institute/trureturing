# Four stars and the missing two-coordinate pattern

## Abstract

Coordinate projections at half-size 28

**Theorem 1.1 (Every coordinate pair realizes all four patterns).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.pair_projection_surjective_of_twenty_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.pair_projection_surjective_of_twenty_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a 72-vertex Huang-balanced induced cubic support in the nine-cube with each coordinate half of size at least 28. If a two-bit pattern is absent, the two specified halves must both have size 28. The opposite seven-dimensional fiber then consists of four disjoint three-leaf stars.

The missing pattern identifies the two adjacent signed fibers. Reducing their signed relation modulo two shows that the opposite occupation is fixed by ordinary adjacency over the field of two elements. The parity defects of the four stars cancel. Coordinate translations and the stabilizer of the first star reduce the cancellation to two residual cases, which force the stars to share their three directions.

In the resulting three-cube by four-cube product, the signed row on each parallel star determines the adjacent fibers. Their cardinality forces a 20-vertex half on a star axis. The cube action carries that cut back to the original support, contradicting the lower bound 28.

**Theorem 1.2 (At least ten patterns on any four distinct axes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.four_projection_card_ge_ten_of_twenty_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.four_projection_card_ge_ten_of_twenty_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair surjectivity allows the antipodal complement-edge argument on any four distinct axes. The eight- and nine-pattern exclusions then give the ten-pattern lower bound for the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.four_projection_card_ge_ten_of_twenty_eight`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp.pair_projection_surjective_of_twenty_eight`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit](Q9NineProjectionOrbit.md)
