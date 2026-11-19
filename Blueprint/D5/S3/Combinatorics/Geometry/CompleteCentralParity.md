# Parity of complete n-central metric graphs

## Abstract

An n-point metric space with n central distances and a complete central graph exists exactly when n=1 or n is even.

**Definition 1.1 (The round-robin space).**

Lean statement: `D5/S3/Combinatorics/Geometry/CompleteCentralParity.Space`

*Formalization.* `D5/S3/Combinatorics/Geometry/CompleteCentralParity.Space` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Space m is the point set {0,…,2m+1}. With M=2m+1 and the point M playing the role of ∞, a pair {i,j} of points below M lies in class (i+j) mod M and a pair {i,∞} in class 2i mod M; this is the round-robin one-factorization of the complete graph on 2m+2 points into M perfect matchings, as in Harary. Distinct points in class r are at distance 1+r/(2m+2), a value in [1,2), so the triangle inequality holds.

**Theorem 1.2 (The parity classification).**

Lean statement: `D5/S3/Combinatorics/Geometry/CompleteCentralParity.complete_central_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CompleteCentralParity.complete_central_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For n ≥ 1, some metric space on n points has exactly n central distances and a complete central graph if and only if n=1 or n is even. For odd n=2k+1 ≥ 3 the edge-cover bound gives at least (n−1)(k+1)=2k(k+1) central edges, more than the k(2k+1) pairs available. For n=1 a single point works. For even n=2m+2 every class is a perfect matching, so each value 1+r/(2m+2) with r<2m+1 is central; together with 0 these are the 2m+2 central values, and every pair of distinct points is at a central distance. This is Theorem 5 of H. Ma and W. Zhang.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CompleteCentralParity.Space`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CompleteCentralParity.complete_central_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/CentralEdgeCover](CentralEdgeCover.md)
