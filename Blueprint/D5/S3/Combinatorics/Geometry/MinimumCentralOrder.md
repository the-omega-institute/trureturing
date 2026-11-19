# Minimum order of a k-central metric space

## Abstract

The least order of a nonempty finite metric space with exactly k central values is 1 for k=1, k for even k and k+1 for odd k ≥ 3.

**Definition 1.1 (The capped round-robin space).**

Lean statement: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.Capped`

*Formalization.* `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.Capped` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Capped m c is the point set {0,…,2m+1} with the round-robin classes of the parity construction. Distinct points in class r are at distance 1+min(r,c)/(2m+2), a value in [1,2), so the triangle inequality holds. Every class is a perfect matching, so for c<2m+1 the central values are 0 and 1+r/(2m+2) for r ≤ c, which makes c+2 of them.

**Theorem 1.2 (The minimum orders).**

Lean statement: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For k ≥ 1, the least order of a nonempty finite metric space with exactly k central values is 1 when k=1, k when k is even, and k+1 when k ≥ 3 is odd. Every central value is a distance to a fixed point, so there are at most as many central values as points. If the two counts agree, the distances to each point are exactly the central values, so the central graph is complete and the parity classification forces the order to be 1 or even. Capped m c with m=⌊(k−1)/2⌋ and c=k−2 has 2m+2 points and k central values for k ≥ 2, and one point serves for k=1. This is Corollary 6 of H. Ma and W. Zhang, answering Problem 4.3 of O. Dovgoshey and O. Rovenska.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.Capped`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order`
- Dependency: [D5/S3/Combinatorics/Geometry/CompleteCentralParity](CompleteCentralParity.md)
