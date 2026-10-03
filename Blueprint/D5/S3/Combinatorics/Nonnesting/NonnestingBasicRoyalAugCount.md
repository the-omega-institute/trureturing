# Augmented Dyck Weights

## Abstract

An extra factor records a singleton first component of a weighted Dyck path.

**Definition 1.1 (Augmented weight sum).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount.augmentedWeight`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount.augmentedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For semilength n, sum two to the power of the number of adjacent downstep pairs plus the number of singleton components after the first component. Multiply each summand by two when the path is nonempty and its first primitive component is a single upstep followed by a downstep.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount.augmentedWeight`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount](NonnestingBasicRoyalGroundCount.md)
