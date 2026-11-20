# The subdivided K₄ projection

## Abstract

Ten patterns in a four-coordinate projection

**Theorem 1.1 (A ten-pattern projection belongs to the subdivided K₄ orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4.ten_projection_only_k4`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4.ten_projection_only_k4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a 72-vertex Huang-balanced induced cubic support in the nine-cube with every coordinate half of size at least 28. Suppose a projection onto four distinct axes realizes ten patterns. Its projected graph is equivalent by coordinate reindexing and bit translation to the graph obtained by subdividing each edge of K₄ once.

Pair coverage gives antipodality of distinct parallel complement edges. Together with projected minimum degree two this leaves six orbits of ten-point subsets under the four-cube action. The signed Huang equations transport to each representative.

Two representatives lose a realized pattern through the exterior equations or equality of suffix supports. For another representative, a mixed signed sum cancels by self-adjointness and bounds a half. Two more have five-cube suffix carriers with six common leaves. Their two-center geometry forces halves of size at most 27.

In the remaining representative the four even patterns are the vertices of K₄ and each odd pattern is the midpoint of a distinct edge. The signed odd values on a suffix fiber can therefore be studied through cuts of K₄. This reduces a projection case in the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4.ten_projection_only_k4`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp](Q9PairProjectionSharp.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint](Q9TenShadowSelfAdjoint.md)
