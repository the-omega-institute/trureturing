# FishburnTenSevenACEquiv

## Abstract

The first and third triple-avoidance classes are parametrized by three-letter words.

**Definition 1.1 (Parameters for the first and third classes).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ACParameters`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ACParameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For a nonnegative size and a Boolean selecting the third class, the parameter set is the disjoint union of a singleton and pairs consisting of a peak between two and the size and a word of length peak minus two. The word belongs to language C when the Boolean is true and to language A when it is false.

**Theorem 1.2 (Word parametrization of two avoidance classes).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ac_equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ac_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every positive size, the Fishburn permutations avoiding 1324, 2143 and 1423 are in bijection with the parameters using language A, and those avoiding 1324, 1423 and 3124 are in bijection with the parameters using language C. The singleton corresponds to the decreasing permutation. A peak and word correspond to the permutation obtained by reconstruction at the given size, with the word assigning the entries from two through peak minus one to the three blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ACParameters`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.ac_equivalence`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses](FishburnTenSevenClasses.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum](FishburnTenSevenMinimum.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal](FishburnTenSevenUnimodal.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding](FishburnTenSevenWordEncoding.md)
