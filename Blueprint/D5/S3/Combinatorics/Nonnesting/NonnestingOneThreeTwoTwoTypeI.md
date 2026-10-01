# Type I Terminal Insertion

## Abstract

Type I inserts the pivot twice after the upper word and preserves 1322 avoidance.

**Definition 1.1 (Type I word).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeIWord`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeIWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The type I word concatenates the upper word, the first cut letters of the lower word, the pivot, the remaining lower letters, and a second pivot.

**Theorem 1.2 (Type I preserves 1322 avoidance).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeI_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeI_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Suppose every upper letter exceeds the pivot, every lower letter is smaller than the pivot, each word has exactly two copies of each of its letters, and both words avoid 1322. If every first occurrence in the lower word lies before the cut, the type I word avoids 1322.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeIWord`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.typeI_avoids`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders](NonnestingBasicOrders.md)
