# Sphere counts characterize minimum-order ultrametric spaces

## Abstract

A finite ultrametric space with center {0 = c_0 < ⋯ < c_h} has 2^(i-1) points at distance c_i from every point, for 1 ≤ i ≤ h, exactly when it has 2^h points.

**Theorem 1.1 (The sphere-count characterization).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

Let X be a finite ultrametric space whose center, the set of t ≥ 0 such that every point has a point at distance t, is exactly {0 = c_0 < c_1 < ⋯ < c_h}. Then every point has 2^(i-1) points at distance c_i for all 1 ≤ i ≤ h if and only if |X| = 2^h, that is, X is minimum-order with this center (MCD). The forward implication does not assume that every distance is central. This is Corollary 11 of H. Ma and W. Zhang (version 3), settling Conjecture 5.5 of Dovgoshey et al.

If the counts hold, the open balls of radius c_h, the diameter, partition X into parts of equal size t with (r - 1)t = 2^(h-1), and each part contains the disjoint spheres of radii c_0, …, c_(h-1) around its points, so t ≥ 2^(h-1); hence r = 2 and |X| = 2^h. Conversely, on an MCD space the two open balls of radius c_h around points at distance c_h are disjoint, keep every lower central value and so each have at least 2^(h-1) points by the minimum-order bound; they therefore have exactly 2^(h-1) points and center {c_0, …, c_(h-1)}, and induction gives the lower spheres while the sphere of radius c_h is the other ball.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts.result`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder](../UltrametricCenterMinimumOrder.md)
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders](../UltrametricCenterSphereOrders.md)
