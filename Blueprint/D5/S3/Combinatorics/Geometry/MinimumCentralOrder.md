# Minimum order of a k-central metric space

## Abstract

The least order of a nonempty finite metric space with exactly k central values is 1 for k=1, k for even k and k+1 for odd k ≥ 3.

**Theorem 1.1 (The minimum orders).**

Lean statement: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For k ≥ 1, the least order of a nonempty finite metric space with exactly k central values is 1 when k=1, k when k is even, and k+1 when k ≥ 3 is odd. The edge-cover bound (k−1)⌈n/2⌉ against the n(n−1)/2 pairs of n points gives k ≤ n, and k ≤ n−1 when n ≥ 3 is odd, so an odd k needs at least k+1 points. For k ≥ 2 the round-robin band on 2m+2 points, m=⌊(k−1)/2⌋, with its first k−1 classes central and every other pair at its own distance has k central values, and one point serves for k=1. This is Corollary 6 of H. Ma and W. Zhang, answering Problem 4.3 of O. Dovgoshey and O. Rovenska.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MinimumCentralOrder.minimum_order`
- Dependency: [D5/S3/Combinatorics/Geometry/CompleteCentralParity](CompleteCentralParity.md)
