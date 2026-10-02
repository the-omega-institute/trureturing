# FishburnTenSevenBParameters

## Abstract

The second triple-avoidance class has parameters describing initial-one tails and interval forms.

**Definition 1.1 (Permutations starting with one).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.HStart`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.HStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For a nonnegative size, this set consists of the Fishburn permutations of that length avoiding 213 whose first entry is one.

**Definition 1.2 (Parameters for the second class).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.BParameters`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.BParameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Choose a maximum between one and the size. Its parameters are the disjoint union of Fishburn permutations of length maximum avoiding 213 and starting with one, and triples consisting of a low between two and maximum minus one, a high between low and maximum minus one, and a Fishburn permutation of length low minus two avoiding 213.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.BParameters`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.HStart`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary](FishburnTenSevenAuxiliary.md)
