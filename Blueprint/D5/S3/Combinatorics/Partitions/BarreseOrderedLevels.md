# Prescribed Ordered Level Numbers

## Abstract

The Gaussian recurrence counts literal fixed-slot source boards, with the published top-down order restored.

**Definition 1.1 (Native cell total).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.levelTotal`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.levelTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For a source board with U columns and mt rows, the p-th bottom-up level total is the sum, over j=0,...,m-1, of the number of columns whose height exceeds mp+j. This counts the actual occupied cells in that level with weight one. It places no singleton restriction on the board.

**Definition 1.2 (The complete source fiber).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.NativeFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.NativeFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

NativeFiber(m,U,a) contains every weakly increasing U-tuple of column heights from zero through m times length(a) with the prescribed bottom-to-top totals a. Every column slot, every empty top row and every zero entry is retained.

**Definition 1.3 (Native boards and flat row fibers).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.nativeRowsEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.nativeRowsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The padded row-column bijection restricts to an exact bijection between NativeFiber(r+1,U,a) and the flat fiber beginning at row bound U. Each row coordinate counts literal source cells, so the restriction preserves all level totals; the inverse reconstructs every source column height.

**Theorem 1.4 (Complete bounded enumeration).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.native_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.native_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every r,U and every finite ordered list a of nonnegative totals, the number of boards in NativeFiber(r+1,U,a) is F(a,U). Thus every positive level size m is obtained with r=m-1. Evaluate G by q-Pascal, use T_a(u,v)=[q^(a-mv)]G(u-v+m-1,m-1) when v<=u and mv<=a and zero otherwise, then use F([],u)=1 and F(a::as,u)=sum_v T_a(u,v)F(as,v). The summation states range only over 0,...,U.

**Theorem 1.5 (The entire fixed ambient source question).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.source2023_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.source2023_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every positive m, every n and every top-down vector l indexed by the n ambient levels, the exact number of weakly increasing n-slot source column tuples with heights at most mn and those level numbers is F((l_n,...,l_1),n), with r=m-1. This is the fixed n-column, n-level ambient convention of Section 2.2. The formula includes empty top levels, all-zero data, m=1, width zero through n and every infeasible vector. No reordering or multiset quotient is used. It does not enumerate the larger rook equivalence class.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.NativeFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.levelTotal`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.nativeRowsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.native_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.source2023_count`
- Dependency: [D5/S3/Combinatorics/Partitions/FerrersLevelGluing](FerrersLevelGluing.md)
