# Combine row and column cuts on one parity table

## Abstract

Combine exact row and column rank deficits in a parity table with odd margins.

**Theorem 1.1 (Mixed rank deficits under odd margins).**

$$\operatorname{OddMargins}\left(n, m\right) \Rightarrow \operatorname{MixedRankDeficits}\left(n, m, R, C\right) \le \operatorname{EligibleIntervalScore}\left(n, m, R, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rows are all even subsets of the coordinates and columns are all odd subsets. The table has a row containing every coordinate. Row and column sums are odd and can vary. Every subtraction is natural subtraction.

The row deficit at a selected threshold is the number of ordinary even rows of at least that weight minus their mass in odd columns of weight at most the complementary rank. The column deficit is the number of odd columns above the complementary rank minus the mass they receive from the full row and all lower-weight rows. A threshold selected on both sides uses the larger of the two deficits.

Sum the resulting deficits over the selected thresholds. The upper bound counts each ordinary cell with odd mass once per positive deficit at a threshold strictly above the complementary column weight and at most the row weight. At each threshold the odd margins ensure enough such cells to pay the selected deficit. The two sides use the same eligible cells.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds](ParityStackedRankBounds.md)
