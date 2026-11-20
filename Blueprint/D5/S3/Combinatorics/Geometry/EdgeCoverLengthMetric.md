# Prescribed central distances from edge-cover packings

## Abstract

Constant lengths on edge-disjoint spanning edge covers of K_n give center {0, a_1, …, a_s} and central edges their union.

**Definition 1.1 (Length data on K_n).**

Lean statement: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LengthData`

*Formalization.* `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LengthData` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Edge-disjoint spanning edge covers F_1, …, F_s of K_n (every vertex lies on an edge of each F_i), distinct class lengths a_1, …, a_s, and a length for every edge outside the classes, these lengths pairwise distinct and different from every a_i; all lengths lie in a band [c, 2c) with c > 0.

**Definition 1.2 (The prescribed metric space).**

Lean statement: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LSpace`

*Formalization.* `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LSpace` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

The n vertices with distance 0 on the diagonal, a_i on the edges of F_i and the prescribed length on every other edge. This is a metric space because in a triangle of distinct vertices the longest side is less than 2c while the other two sum to at least 2c.

**Theorem 1.3 (Center and central edges of the prescribed metric).**

Lean statement: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For n ≥ 3 the metric has distance a_i on the edges of F_i and the prescribed length on the remaining edges, its center is C(X) = {0, a_1, …, a_s}, and two vertices are joined in the central graph exactly when they are joined in some F_i.

Each a_i is central because F_i covers every vertex. A nonzero central value is a distance from vertex 0; if it were a length outside the classes, a vertex z off that unique edge would need an edge of the same length at z, which is a different edge with the same length, impossible. So the positive central values are exactly the a_i, and the central edges are the class edges. This is equation (1) of H. Ma and W. Zhang (DOI 10.5281/zenodo.24369118), with the band [1, 2) generalized to [c, 2c); it uses the narrow-band principle of O. Dovgoshey and O. Rovenska (arXiv:2610.11596, proof of Theorem 3.8, formula (19)).

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LSpace`
- Truth anchor: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.LengthData`
- Truth anchor: `D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric.result`
- Dependency: [D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges](DovgosheyRovenskaCentralEdges.md)
