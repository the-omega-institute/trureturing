# Gluing Ordered Levels

## Abstract

The last-row bound is exactly the information needed to glue successive levels of the same Ferrers board.

**Definition 1.1 (Exact gluing bijection).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flatPathsEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flatPathsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every r,U,a,u, cut the flat row tuple into consecutive blocks of r+1 rows. The last row v of the first block bounds every row of the remainder because the full tuple is decreasing. Conversely, a first block ending at v and a decreasing remainder bounded by v concatenate to a decreasing tuple. These two operations are mutually inverse and preserve every ordered block sum. Induction includes the unique empty tuple and empty path.

**Theorem 1.2 (All flat rows are counted).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flat_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flat_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The cardinality of the complete flat fiber equals F(a,u). There are no omitted compatibility conditions between the blocks: the inverse gluing proof establishes global weak decrease across each boundary. The count applies to zero rows, zero dimensions and infeasible ordered totals.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flatPathsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelGluing.flat_card`
- Dependency: [D5/S3/Combinatorics/Partitions/FerrersLevelCounting](FerrersLevelCounting.md)
