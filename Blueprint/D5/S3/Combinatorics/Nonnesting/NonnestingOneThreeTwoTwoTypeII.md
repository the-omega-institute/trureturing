# Type II Terminal Insertion

## Abstract

Type II interleaves two copies of a lower order with the upper word and preserves 1322 avoidance.

**Definition 1.1 (Type II word).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeIIWord`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeIIWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The type II word concatenates the first cut letters of the upper word, the lower order, the pivot, the remaining upper letters, the lower order again, and a second pivot.

**Theorem 1.2 (Type II preserves 1322 avoidance).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeII_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeII_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Suppose every upper letter exceeds the pivot, every letter of the lower order is smaller than the pivot, the upper word has exactly two copies of each of its letters, and the lower order has distinct entries. If the upper word and the concatenation of two copies of the lower order avoid 1322, and every first occurrence in the upper word lies before the cut, the type II word avoids 1322.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeIIWord`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.typeII_avoids`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders](NonnestingBasicOrders.md)
