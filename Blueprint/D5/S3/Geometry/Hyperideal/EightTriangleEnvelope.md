# Adjacent degree-eight packets: exact endpoint margins

## Abstract

A strict hyper-ideal CFMP subcase covers global degree-eight edges and high edges of degree at least twelve. In each tetrahedron the degree-eight local edges form a three-star, three-cycle, or four-cycle, so each low edge has exactly two low neighbours. The degree-fourteen mixed packet is the new threshold.

With a=5/4 and c=10/7, the lower-face cosines are 73/100, 8 sqrt(6)/27, and 293/400; the upper-face cosines are 709/1003, 11 sqrt(249)/249, and 2753/4012. Their squared margins are on the strict sides of 1/2. A high edge has upper cosine at most 53/59, and the exact alternating Taylor comparison at 22/49 gives 5965/6972 < cos(pi/6), so fourteen occurrences force cone angle greater than 2 pi.

**Theorem 1.1 (High-edge Taylor margin).**

$$high_upper_sq$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/EightTriangleEnvelope.high_upper_taylor`. The surrounding six-variable formula, monotonicity, topology and co-volume minimum are cited ordinary mathematics in `docs/develop/theory/CFMP_EIGHT_TRIANGLE_CLUSTERS.md`. ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint arithmetic is exact and no finite numerical sampling is used. The full theorem minimizes the actual shared-edge co-volume on a compact global box; it does not assume a zero-curvature solution. An explicit 16-tetrahedron orientable packet with global degrees 8,8,8,8,8,8,14,34 is included in the theory document.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/EightTriangleEnvelope.high_upper_taylor`
- Theory: [CFMP_EIGHT_TRIANGLE_CLUSTERS](../../../../../../docs/develop/theory/CFMP_EIGHT_TRIANGLE_CLUSTERS.md)
