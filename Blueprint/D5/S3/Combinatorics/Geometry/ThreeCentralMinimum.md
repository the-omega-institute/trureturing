# The sharp three-central minimum

## Abstract

For every n ≥ 4 the least number of central edges of a three-central n-point metric space is 2⌈n/2⌉.

**Definition 1.1 (The narrow-band space).**

Lean statement: `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.Space`

*Formalization.* `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.Space` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Space N is the point set {0,…,n−1} with n=N+4. The pairs {2k,2k+1} (closed by {0,n−1} when n is odd) are at distance 1; the pairs {2k+1,2k+2} (closed by {0,n−1} when n is even and by {0,2} when n is odd) are at distance 2; each of these two classes has ⌈n/2⌉ pairs and covers every point, and the classes are disjoint. Every other pair {i,j} with i<j is at distance 1+(n·i+j+1)/(n²+1), a value strictly between 1 and 2 that no other pair takes. All nonzero distances lie in [1,2], so the triangle inequality holds.

**Theorem 1.2 (The minimum is 2⌈n/2⌉).**

Lean statement: `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.three_central_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.three_central_minimum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For every n ≥ 4, every three-central metric space on n points has at least 2⌈n/2⌉ central edges, and the narrow-band space attains 2⌈n/2⌉. The lower bound is the edge-cover bound with k=3. In the narrow-band space 0, 1 and 2 are central. Any other central value t is the distance of a single pair, since distances outside the two classes determine their pair; a third point would then have no partner at distance t. So the center is {0,1,2}, the central edges are exactly the two classes, and there are at most 2⌈n/2⌉ of them. This is Theorem 3 of H. Ma and W. Zhang.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.Space`
- Truth anchor: `D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.three_central_minimum`
- Dependency: [D5/S3/Combinatorics/Geometry/CentralEdgeCover](CentralEdgeCover.md)
