# The sharp three-central ultrametric minimum

## Abstract

A three-central ultrametric on n ≥ 4 points has at least 2n−4+⌈n/2⌉ central edges, with an explicit equality criterion and an attaining space.

**Definition 1.1 (The attaining ultrametric).**

Lean statement: `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.Tree`

*Formalization.* `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.Tree` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Tree n is the point set {0,…,n−1} split into a part A={0,1} and a part B. B consists of the pairs {2k,2k+1} and, for odd n, the triple {n−3,n−2,n−1} with n−3 designated. Points in different parts are at distance 2, in different components of the same part at 3/2, at different positions of one component at 1, and the two undesignated points of the triple at 1/2. Distances depend only on the first level where two points differ and decrease along the levels, so the metric is an ultrametric. Its center is {0,1,2}: the row of 0 contains only these values, and every point has a neighbour at 1 and one at 2.

**Theorem 1.2 (The minimum and its equality criterion).**

Lean statement: `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.ultra_three_central_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.ultra_three_central_minimum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For n ≥ 4 every three-central ultrametric on n points has at least 2n−4+⌈n/2⌉ central edges. Its center is {0,a,D} with D the maximum distance, which is central and equal to the diameter. The points at distance below D from a fixed point form a class S; by the ultrametric inequality every point of S is at distance D from every point outside S, and S and its complement each contain a point with its a-neighbour, so there are at least |S|(n−|S|) ≥ 2(n−2) edges of length D, while the length a has at least ⌈n/2⌉ edges. Equality holds exactly when the diametrical graph is complete bipartite with a part of two points and the non-diametrical central edges number ⌈n/2⌉, and Tree n attains it. This is Theorem 4 of H. Ma and W. Zhang; the centrality of D agrees with Theorem 2.15 of O. Dovgoshey and O. Rovenska.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.Tree`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.ultra_three_central_minimum`
- Dependency: [D5/S3/Combinatorics/Geometry/CentralEdgeCover](CentralEdgeCover.md)
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders](UltrametricCenterSphereOrders.md)
