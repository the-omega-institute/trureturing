# Rank jumps at budget 640 in dimension fourteen

## Abstract

Bound the jump count for a factor at the fourteen-coordinate budget ceiling.

**Definition 1.1 (Ordinary rank jumps).**

$$\operatorname{RankJumps}\left(f\right) = \operatorname{StrictRankSkippingEdges}\left(f\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.rankJumps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite vertex set with natural-number ranks, a Boolean edge table, and a distinguished vertex t, retain the true entries from rows other than t whose target rank exceeds the source rank by at least two.

**Theorem 1.2 (At least two ordinary jumps in dimension fourteen within budget 640).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.two_jumps_at_640`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.two_jumps_at_640` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any marked coordinate among fourteen, and a Boolean table between the two copies of the subsets of the other thirteen coordinates. Outside the full-set row, a true entry requires inclusion. At multiplier three each ordinary row and column has odd degree at most three. The full row and column both use the same degree mode: even degree at most two when selected, odd degree at most one otherwise. The cost is four times the sum of one and the number of true entries from ordinary odd rows to odd columns. If the cost is at most 640, there are at least two true entries from ordinary rows whose target rank exceeds the source rank by at least two.

The deficits at ranks one, three and eleven force at least 9, 100 and 50 chargeable diagonals. A budget of 640 leaves 159 chargeable ordinary entries, so those deficits exhaust the charge. The exceptional prefix inflow saturates at two, and the charged diagonals at ranks five, seven and nine vanish. Their layer-cardinality parities are odd, even, odd. The cut parity identity transfers this pattern to ordinary jumps. The four changes after zero padding require at least two jumps.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.rankJumps`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps.two_jumps_at_640`
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity](../../../Combinatorics/Graph/RankCuts/RankedIntervalParity.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
