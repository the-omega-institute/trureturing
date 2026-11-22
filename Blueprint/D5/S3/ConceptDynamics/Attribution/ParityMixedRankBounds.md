# Combine row and column cuts on one parity table

## Abstract

Compatible row and column rank deficits for an odd-margin parity table.

**Theorem 1.1 (Mixed rank deficits under odd uniform margins).**

$$\operatorname{OddUniformMarginsAndDisjointCuts}\left(n, k, R, C, m, q\right) \Rightarrow \operatorname{FullRowScore}\left(n, b\right) + \operatorname{MixedRankDeficits}\left(n, k, R, C\right) \le \operatorname{IntervalWeightedCount}\left(n, m, b\right) + \operatorname{ChargedPositiveDeficitCount}\left(n, k, R, C, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension n is even. Each row and column of the natural-number table has the same odd marginal k. Rows are all even subsets of the coordinates and columns are all odd subsets. The finite sets R and C of natural-number thresholds are disjoint. The chosen column q has positive mass in the full row.

Each ordinary cell contributes its rank interval length times its mass modulo two. Each full-row cell contributes its column weight times its flag. Differences between natural numbers are truncated at zero.

The bound starts with the full-row score. For each r in R, add the positive part of one plus the number of ordinary even rows of weight at least r, minus k times the number of odd columns of weight at most n minus r. For each r in C, add the positive part of one plus the number of odd columns of weight greater than n minus r, minus k times the quantity one plus the number of even rows of weight below r. The additional allowance in that estimate accounts for the full row.

For each ordinary cell, assign every threshold that charges that cell to a distinct position in the integer interval from n minus the column weight, excluded, to the row weight, included. Its length is the intersection size minus the number of coordinates missed by both profiles, using natural-number subtraction. Count a selected threshold on the right-hand side when its deficit is positive and q has weight greater than n minus r. For a positive deficit at any other threshold, the mass in q improves the capacity estimate by one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds.mixed_rank_lower`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds](ParityStackedRankBounds.md)
