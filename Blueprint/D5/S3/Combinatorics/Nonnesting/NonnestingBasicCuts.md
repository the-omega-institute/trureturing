# Separated Value Cuts

## Abstract

Order separation splits a doubled word.

**Theorem 1.1 (Filtering a separated word).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.filter_partition_of_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.filter_partition_of_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

If every entry at most k precedes every larger entry, the word is the concatenation of its two value filters.

**Theorem 1.2 (Separation gives a value cut).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.valueCut_of_separated_indices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.valueCut_of_separated_indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

In a doubled permutation, separation of entries at most k from larger entries establishes a value cut at k.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.filter_partition_of_separated`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.valueCut_of_separated_indices`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](NonnestingBasicSum.md)
