# A half-size bound from signed self-adjointness

## Abstract

Signed fibers of a ten-pattern projection

**Theorem 1.1 (A weighted bound on two fibers and one coordinate half).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_global_inequality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_global_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the projection of a Huang-balanced induced cubic nine-cube support onto the first four coordinates is contained in {0,1,2,3,4,5,10,11,12,14}, using the first coordinate as the low bit. Let w₀ and w₂ be the fiber sizes at codes 0 and 2, and let h count the vertices with that bit set. Then 4(w₀ + w₂) + 3h is at most twice the support size.

The exterior Huang equations express each signed fiber using four entries in {−1,0,1}. A finite check on those parameters gives a weighted occupation inequality with a mixed term between the signed slices at codes 1 and 3. On summing over the five remaining coordinates, the mixed term vanishes by self-adjointness of the signed adjacency.

**Theorem 1.2 (Exclusion of the exact ten-pattern projection at half-size 30).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_excluded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_excluded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The slices at codes 0 and 2 satisfy the five-cube parity equation after reducing the signed row equations modulo two. Exact projection makes these slices nonempty. Each has induced degree at most three and hence at least eight vertices. With 72 vertices in the support and h at least 30, the weighted bound would give 154 at most 144.

This removes the indicated projection in the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_excluded`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint.tenShadow_global_inequality`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9GridProjection](Q9GridProjection.md)
