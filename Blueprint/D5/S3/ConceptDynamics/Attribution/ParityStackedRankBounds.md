# Add high even rank deficits for one common table

## Abstract

Simultaneous rank deficits for an odd-margin parity table.

**Theorem 1.1 (Rank deficits under odd uniform margins).**

$$\operatorname{OddUniformMargins}\left(n, k, R, m, b\right) \Rightarrow \operatorname{RankDeficits}\left(n, k, R\right) \le \operatorname{IntersectionCount}\left(n, m, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds.stacked_fixed_from_odd_margins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension n is even and at least six. Each row and column of the natural-number table has odd marginal k. Rows range over all even subsets of the n coordinates, and columns range over all odd subsets. The thresholds form a finite set of natural numbers in [4, n minus 2]. At least one column has a positive full-row flag bounded by the corresponding full-row mass.

Each ordinary cell contributes its mass modulo two times the size of the intersection of the row and column. Each cell in the full row uses its flag instead.

The lower bound starts with one and adds the positive part of the number of weight-(n minus 1) odd columns plus one minus 2k. For each threshold r it also adds the positive part of one plus the number of ordinary even rows of weight at least r minus k times the number of odd columns of weight at most n minus r.

A cell with row p and column q can count toward several cuts. Their distinct thresholds occupy places in the integer interval (n minus the size of q, the size of p]. The interval has at most as many places as the intersection. For a nonempty ordinary row and a column of size n minus 1, position 2 is reserved for the top-column charge.

A positive full-row flag at column q provides at least the size of q. That covers one baseline unit, one top-column unit when q has size n minus 1, and one unit for each threshold r greater than n minus the size of q.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds.stacked_fixed_from_odd_margins`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds](ParityOddRankBounds.md)
