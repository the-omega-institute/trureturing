# Edge-cover lower bound for central graphs

## Abstract

A finite metric space with n points and k central distances has at least (k−1)⌈n/2⌉ central edges.

**Theorem 1.1 (The edge-cover bound).**

Lean statement: `D5/S3/Combinatorics/Geometry/CentralEdgeCover.edge_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CentralEdgeCover.edge_cover_bound` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Let X be a finite metric space with n points. Its center C(X) is the set of t ≥ 0 such that every point has a point at distance t, and the central graph joins distinct points whose distance lies in C(X). If C(X) has k elements, the central graph has at least (k−1)⌈n/2⌉ edges. For the empty space the center is all of [0,∞), whose cardinality is recorded as 0, so the bound is 0. Since d(x,x)=0, zero is central. For each nonzero central value t choose for every x a point at distance t from x; it differs from x, so x lies on a central edge of length t. Each edge has two endpoints, so the edges of length t number at least ⌈n/2⌉. Edges of different lengths are distinct, and summing over the k−1 nonzero central values gives the bound. This is Lemma 2 of H. Ma and W. Zhang, refining the central-graph bound of O. Dovgoshey and O. Rovenska.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CentralEdgeCover.edge_cover_bound`
- Dependency: [D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges](DovgosheyRovenskaCentralEdges.md)
