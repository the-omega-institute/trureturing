# The eleven-pattern bound

## Abstract

Four-coordinate projections of order-72 balanced cubic supports

**Theorem 1.1 (At least eleven patterns on any four distinct axes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjectionEleven.four_projection_card_ge_eleven_of_twenty_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjectionEleven.four_projection_card_ge_eleven_of_twenty_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a 72-vertex induced cubic support in the nine-cube be Huang-balanced and have at least 28 vertices in each coordinate half. Its projection onto any four distinct axes realizes at least eleven patterns. The ten-pattern lower bound and orbit classification reduce the proof to the subdivided K₄.

Over each suffix in the five-cube, the occupied midpoint patterns are the crossing edges of a K₄ cut. Counting occupied even patterns over zero cuts gives two possibilities. Zero such vertices force all four star halves to have size 30, which the tight-star obstruction excludes. Eight such vertices force all four star halves to have size 28 and leave exactly 40 occupied midpoint patterns counted across the suffixes.

The coupled signed rows reduce modulo two to the adjacency fixed-point equation on the five-cube for the singleton-cut indicator. If there are s singleton cuts and b balanced cuts, the midpoint count is 3s + 4b = 40. The fixed-point size restriction leaves 0, 8, 12 or 16 singleton cuts before the midpoint budget excludes 16. At zero, all midpoint-bearing fibers lie in one connected suffix graph with a common balanced cut, so only four of the six midpoint patterns occur. At eight and twelve, the cut-overlap degree equations and the restrictions on adjacent occupied centers rule out the required suffix incidences.

This bound restricts the order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2. The external problem remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjectionEleven.four_projection_card_ge_eleven_of_twenty_eight`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp](Q9PairProjectionSharp.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4](Q9TenProjectionOnlyK4.md)
