# An obstruction from overlapping coordinate translations

## Abstract

Two endpoint translations exclude a single common partner of two cubic contact axes.

**Theorem 1.1 (Two cubic contact axes cannot have exactly one common partner).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CubicContactCommonPartner.no_single_common_partner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CubicContactCommonPartner.no_single_common_partner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a realized contact on axes i and j. The other partners of i are a and d, and those of j are c and d. Translate the contact by c and d and inspect its midpoint reached along i. The original contact and its translate by a and d rule out the two additional opposite-side neighbors. Either neighbor would realize the missing pair i and c. The midpoint then has one neighbor on the opposite support and violates exterior parity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CubicContactCommonPartner.no_single_common_partner`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit](Q9DegreeThreeContactOrbit.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph](Q9SquareMaskGraph.md)
