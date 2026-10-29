# A Width Bound from the Level Data

## Abstract

The unrestricted normalized shape fiber is finite because its bottom level bounds its width.

**Definition 1.1 (Levels of a normalized shape).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.shapeLevel`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseAllWidths.shapeLevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For a finite Young diagram with bottom-to-top row coordinates, shapeLevel(m,mu,p) is the sum of the lengths of rows mp through mp+m-1. This is the same cell statistic as in a normalized, right-aligned source board.

**Definition 1.2 (No imposed width or height bound).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.ShapeFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseAllWidths.ShapeFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

ShapeFiber(m,a) contains all finite Young diagrams whose p-th level total equals the p-th entry of a for p below length(a), and zero for every higher p. Neither width nor height appears as a hypothesis. When the entries of a are positive, length(a) is exactly the highest nonempty level.

**Theorem 1.3 (The derived width bound).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.width_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseAllWidths.width_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every shape in ShapeFiber(r+1,a), the number of positive source columns is its bottom row length. This length is at most the sum of the r+1 rows in the bottom level, hence at most a_1, with a_1=0 for the empty list. Every row is no longer than the bottom row.

**Definition 1.4 (Unique padding to the derived bound).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.normalizedPaddingEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/BarreseAllWidths.normalizedPaddingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

There is an exact bijection between ShapeFiber(r+1,a) and NativeFiber(r+1,a_1,a). The zero extension above a forces row (r+1) times length(a) to be empty, hence bounds the height. The width bound permits reading all rows in a_1 column slots. Reflecting to source columns inserts exactly the required number of zero columns at the left. The inverse removes this ambient padding by taking the finite diagram. Thus all positive widths are included, rather than assumed bounded in the definition of the fiber.

**Theorem 1.5 (All normalized widths).**

Lean statement: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.all_width_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BarreseAllWidths.all_width_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every r and a, the cardinality of the unrestricted normalized shape fiber is F(a,a_1). The exact padding bijection reduces its count to native_count. The empty list has the unique empty shape under the stated zero-extension convention; no infinite horizontal family is substituted for this finite normalized count.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.ShapeFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.all_width_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.normalizedPaddingEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.shapeLevel`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BarreseAllWidths.width_bound`
- Dependency: [D5/S3/Combinatorics/Partitions/BarreseOrderedLevels](BarreseOrderedLevels.md)
