# Four parallel covers force a negative signed walk

## Abstract

Four parallel covers force a negative signed walk

**Theorem 1.1 (An edge of the common exterior boundary has at most three covers per component).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover.cover_card_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover.cover_card_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider disjoint separated Huang-balanced cubic supports C and D. If both endpoints of an exterior edge have neighbors in both supports, then at most three edges of C can cover it by a parallel one-coordinate translation. Exchanging C and D gives the same bound on the other side.

Four parallel C-edges would leave too few distinct directions for a parallel D-edge. If the D-neighbor directions at the two exterior endpoints are disjoint, cubicity forces a closed D-walk with coordinate word ℓ,k,i,j,k,ℓ,i,j.

Distinct signed coordinate flips anticommute. The word acts as minus the identity, which contradicts switching balance along a closed walk. The obstruction constrains self-collisions and mixed collisions for arbitrary pairs in the 258-vertex problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover.cover_card_le_three`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord](../TwentyPointEightWord.md)
