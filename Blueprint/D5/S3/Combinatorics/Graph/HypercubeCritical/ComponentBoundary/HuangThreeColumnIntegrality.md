# Even coefficients for three signed cube columns

## Abstract

Even coefficients for three signed cube columns

Hong, Wu and Xia's Problem 2 asks whether the two-neighbor sensitivity of the nine-cube is 3 or 4. In a candidate fold along one coordinate, a dimer occupies both endpoints of an axial edge. Each endpoint has at most two other occupied neighbors by the degree-three bound. At most four of the eight neighboring fibers of a dimer are therefore occupied, leaving at least four empty rows. In the 18+3 case the three dimers of the smaller parity class give three columns on the common set R of empty rows. https://arxiv.org/html/2610.09483v1#Thmproblem2

Suppose the unit-weight axial expansion gives the equation Bc = −(HΛHb)|R. Here H is the full signed Huang adjacency of the eight-cube, b is an integral signed indicator of the majority dimers and B consists of the three opposite columns restricted to R, with their chosen column signs. On the support of Hb, Λ is diagonal with entries +1 or −1, according to the singleton layer. It can be extended by +1 elsewhere because Hb vanishes there. Modulo two, H becomes ordinary adjacency A and Λ becomes the identity. The residual reduces to A² times the indicator of the majority dimers. The even-dimensional identity BinaryKernelCoordinateMoment.adjacency_adjacency_eq_zero gives A² = 0. The theorem below then gives an even integer for each amplitude in c.

**Theorem 1.1 (Even row sums force even coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality.even_coefficients_of_three_cube_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality.even_coefficients_of_three_cube_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vertices are finite coordinate sets and nearest neighbors differ by one coordinate. Choose three distinct centers labeled 0, 1 and 2 and one common finite set of rows. Each column is zero off its center's neighbors on those rows and has entry 1 or −1 at every included neighbor. The common row set contains at least four neighbors of center 0, at least three of center 1 and at least one of center 2. Even integer row sums force all three real coefficients to be even integers.

Distinct centers with a common neighbor differ in two coordinates and can share at most two neighbors. If at least one pair involving center 0 has no common neighbor, the neighborhood of center 0 overlaps the union of the other neighborhoods in at most two rows. If center 0 shares neighbors with both and centers 1 and 2 share none with each other, center 1 has at most two neighbors in the union of the other neighborhoods. If all three pairs share a neighbor, translate center 0 to the empty set. The other two centers are distinct two-element sets whose symmetric difference has size two. Their common coordinate gives a neighbor of all three centers in the full cube, so the two pairwise intersections at center 0 have union of size at most three. These bounds leave a retained row that isolates column 0 or column 1.

The isolated row determines the first coefficient up to sign. Subtracting that column's contribution preserves evenness of every row. The remaining column among 0 and 1 has at least three retained neighbors and shares at most two with center 2. A row outside the neighborhood of center 2 gives the second even coefficient. After subtracting both contributions, any retained neighbor of center 2 gives the last even coefficient.

Four signed Huang columns can admit half-integer amplitudes. Take four singleton centers and retain the empty vertex and the six two-element vertices on their axes. Each column has four entries. Normalize the column signs so each entry at the empty vertex is +1. The two entries on each pair row are opposite by anticommutation of the two signed flips, so a zero target on every pair row forces all four amplitudes equal. Target 2 at the empty vertex then forces each amplitude to be 1/2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality.even_coefficients_of_three_cube_columns`
