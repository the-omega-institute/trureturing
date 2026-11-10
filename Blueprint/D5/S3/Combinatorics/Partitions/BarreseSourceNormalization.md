# The Normalized Source l-Fiber

## Abstract

Positive left-to-right column tuples give an explicit all-width source carrier for the l-operator.

**Definition 1.1 (Normalized source tuples).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.PositiveColumns`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.PositiveColumns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

A normalized source board is a finite weakly increasing list of strictly positive column heights. Deleting leading zero columns from the padded source tuple gives this representative. The empty list represents the empty board. Width and height are both unrestricted in this carrier.

**Definition 1.2 (Finite diagrams and positive source columns).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.normalizedColumnsEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.normalizedColumnsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Transpose a finite Young diagram, take its positive row-length list, then reverse that list to obtain the source left-to-right column heights. The inverse reverses a positive source tuple, forms its Young diagram and transposes. The existing positive row-length equivalence proves that the two maps are inverse. This fixes normalization and right alignment.

**Definition 1.3 (Literal cells in a normalized source level).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.columnLevel`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.columnLevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The p-th bottom-up level total is the sum over its m rows of the number of positive source column heights exceeding the absolute row index mp+j. The column/diagram correspondence preserves these literal cell totals in every level, including all levels above the board.

**Definition 1.4 (Exact l-operator data).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.LFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.LFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

LFiber(m,c) consists of every positive source column tuple whose bottom-up totals are the reverse of c and zero thereafter, with every entry of c strictly positive. For nonempty c this is exactly the trimmed top-down tuple in Definition 4 of Barrese, Loehr, Remmel and Sagan, arXiv:1508.05944v1: each displayed level is nonempty and every higher one is empty. An explicit zero in a nonempty target tuple is rejected. The empty-board extension used here is l(empty)=[], which is stated separately because that definition does not define its largest nonempty level.

**Theorem 1.5 (The entire normalized all-width source count).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.source2015_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.source2015_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every positive m and every finite target tuple c, the cardinality of LFiber(m,c) is zero if c has a nonpositive entry; otherwise it is F(reverse(c),last(c)), with the empty-list bound taken as zero. The original singleton targets are included, while the unknown input boards are unrestricted Ferrers boards. The source-to-diagram and derived-padding bijections establish this formula for all widths and all allowed heights. For a singleton target with t positive entries, the uppermost level is nonempty, so heights range from m(t-1)+1 through mt.

**Definition 1.6 (The native trimmed l-operator).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Start with the literal bottom-up level cell totals. These totals decrease weakly, and finiteness of the board supplies an empty level. Let t be the first empty level index. The operator reverses the list of totals at indices zero through t-1. Thus t is exactly the largest nonempty level in the source's one-based numbering, and the empty board has the stated empty-tuple extension.

**Definition 1.7 (Exact operator fiber correspondence).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.operatorFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.operatorFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The native equality lOperator(m,B)=c is equivalent to the absolute-level specification LFiber(m,c). The forward map uses positivity before the first zero and vanishing afterwards. The reverse map uses uniqueness of a positive finite list from its zero-extended entries: neither an appended zero nor a reordered tuple can represent the same data.

**Theorem 1.8 (Evaluation of the native l-operator fiber).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every positive m and every c, the number of arbitrary-width positive source column tuples B satisfying lOperator(m,B)=c is the same guarded Gaussian recurrence as source2015_count. No width bound is supplied as a premise: last(c), or zero for the empty list, is derived from the bottom-level total. This is the prescribed l-fiber count of Section 6.2 of arXiv:1508.05944v1 under normalized source-column notation. Counting all possible horizontal translations in an unbounded absolute grid is a different carrier; in the fixed 2023 rectangle all literal column positions remain fixed instead.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.LFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.PositiveColumns`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.columnLevel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.normalizedColumnsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.operatorFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.source2015_count`
- Dependency: [D5/S3/Combinatorics/Partitions/BarreseAllWidths](BarreseAllWidths.md)
