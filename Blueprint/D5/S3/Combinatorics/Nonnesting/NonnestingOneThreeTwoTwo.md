# Enumeration of Nonnesting Permutations Avoiding 1322

## Abstract

Nonnesting permutations avoiding 1322 have the asserted binomial enumeration.

**Theorem 1.1 (The 1322 enumeration).**

$$claim1322$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/elizalde-luo-nonnesting-1322` (proved) by `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elizalde-luo-nonnesting-1322","declaration_gid":"D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For every positive n, n times the number of nonnesting permutations of the multiset with two copies of each letter from one through n avoiding 1322 equals the sum, over k from zero through n minus one, of the product of the binomial coefficients choosing k from 3n and choosing n minus one from 2n minus k minus two.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount](NonnestingOneThreeTwoTwoCount.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel](NonnestingOneThreeTwoTwoKernel.md)
