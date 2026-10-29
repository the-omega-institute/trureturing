# Finite Ordered Level Recurrence

## Abstract

The local Gaussian coefficients combine through a finite state consisting of the previous last-row length.

**Definition 1.1 (Compatible levels).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.Paths`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.Paths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For a bottom-to-top list a, Paths(r,U,a,u) is the set of all consecutive prescribed levels beginning below the row bound u. A nonempty path chooses its first last-row length v in {0,...,U}, a level of total a_1 with bound u and last row v, and the remaining path with bound v. The empty list has one empty path.

**Definition 1.2 (Evaluated finite recurrence).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.count`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Define F([],u)=1 and F(a::as,u)=sum over v=0,...,U of T_a(u,v)F(as,v). The total starting value is F(a,U). Every summation runs over the U+1 possible row bounds, rather than over boards. Together with q-Pascal for the Gaussian polynomial, this is an explicit finite evaluation on the original data.

**Theorem 1.3 (Cardinality of compatible levels).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.paths_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.paths_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every r,U,a,u, the number of compatible paths equals F(a,u). The proof splits a nonempty path into its unique first state, first level and remainder; finite dependent-sum and product cardinalities give the recurrence, and level_card supplies each entry.

**Definition 1.4 (Absolute row position).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.rowIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.rowIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For a level size m, t levels, a level index p and a within-level index j, rowIndex is the ambient index mp+j in the mt-row tuple. The finite-index bound is part of the definition, so zero dimensions introduce no artificial row.

**Definition 1.5 (Flat row fiber).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.FlatFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.FlatFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

A flat fiber consists of a weakly decreasing tuple of (r+1) times length(a) row lengths in {0,...,U}, bounded by u, with each consecutive block of r+1 rows summing to the corresponding ordered entry of a. No permutation of a is taken.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.FlatFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.Paths`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.paths_card`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelCounting.rowIndex`
- Dependency: [D5/S3/Combinatorics/Partitions/FerrersLevelTransfer](FerrersLevelTransfer.md)
- Dependency: [D5/S3/Combinatorics/Partitions/FerrersRowCoordinates](FerrersRowCoordinates.md)
