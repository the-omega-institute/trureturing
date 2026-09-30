# Counting Increasing-Order Words

## Abstract

Increasing first-occurrence order admits a binary extension at each positive size.

**Definition 1.1 (Words with increasing first occurrences).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

These are four-pattern avoiders whose first occurrences follow increasing letter order.

**Definition 1.2 (Binary extension equivalence).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingStep`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For positive n, a choice of one of two extensions and a word of size n correspond bijectively to an increasing-order word of size n plus one.

**Theorem 1.3 (Cardinality of increasing-order words).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For positive n, the number of increasing-order words of size n is two to the power n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingStep`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.increasingWords_card`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingFourRecursive](NonnestingFourRecursive.md)
