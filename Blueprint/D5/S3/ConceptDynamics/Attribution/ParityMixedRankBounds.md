# Combine parity mismatches on row and column cuts

## Abstract

Combine exact row and column parity mismatches at selected rank thresholds.

**Theorem 1.1 (Mixed rank deficits for arbitrary margins).**

$$\operatorname{MismatchCount}\left(m, R, C\right) \le \operatorname{ChargedOddCellScore}\left(m, R, C\right) \land \operatorname{CellChargesBoundedByOrdinaryIntersection}\left(m, R, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rows are even subsets of the coordinates and columns are odd subsets. Fix a distinguished row. The table entries are natural numbers. Row and column margins can have either parity.

At a selected row threshold, consider rows of at least that weight outside the distinguished row. Count those whose total mass and mass in columns at or below the complementary rank have different parity. At a selected column threshold, consider columns above the complementary rank. Count those whose total mass and mass received from the distinguished row and lower-weight rows have different parity.

Use the larger count at each threshold and choose rows in a tie. Only odd cells on the chosen side, incident to a counted row or column and lying outside its free block, contribute to the score. The sum of the larger counts is at most this score. The distinguished row contributes zero. For every other cell, its contributing thresholds lie strictly above the complementary column rank and at most the row weight, so their number is at most the size of the row and column intersection.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds](ParityStackedRankBounds.md)
