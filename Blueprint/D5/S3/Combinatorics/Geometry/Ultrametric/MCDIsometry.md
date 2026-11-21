# Isometry rigidity of minimum-order ultrametric spaces

## Abstract

Minimum-order finite ultrametric spaces with equally many points are isometric exactly when their centers of distances coincide.

**Theorem 1.1 (Equal centers characterize isometry).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry.result` (`✓ std3`). ∎

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the center of distances of finite ultrametric spaces*. DOI: [10.48550/arXiv.2603.25850](https://doi.org/10.48550/arXiv.2603.25850). URL: <https://arxiv.org/abs/2603.25850v1>.

*Commentary.*

Let X be a finite ultrametric space with |X| = 2^(|C(X)| - 1), where C(X) is the center of distances, and let Y be a finite ultrametric space that has as many points as X or also satisfies |Y| = 2^(|C(Y)| - 1). Then C(X) = C(Y) if and only if X and Y are isometric. This is Conjecture 4.3 of O. Dovgoshey and O. Rovenska, proved as Corollary 4.3 (with Theorem 4.2) of Dovgoshey, Jaiswal, Kainth, Kaur and Rovenska.

Isometric spaces have the same center. Conversely, with common center {c_0 < ⋯ < c_n}, let m = c_n, which is the diameter. In X take points p and q at distance m; the open balls of radius m around them are disjoint and keep every lower central value, so each has at least 2^(n-1) points by the minimum-order bound, hence exactly 2^(n-1), and together they cover X. Each half is minimum-order with center {c_0, …, c_(n-1)}, and likewise in Y. By induction the halves are isometric, and the two isometries glue to an isometry X → Y, since points in different halves are at distance m on both sides.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry.result`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder](../UltrametricCenterMinimumOrder.md)
