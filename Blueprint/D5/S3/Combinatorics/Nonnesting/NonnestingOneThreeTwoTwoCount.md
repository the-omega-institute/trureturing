# Weighted Terminal Enumeration

## Abstract

Terminal factorization decomposes weighted counts on every nonempty finite alphabet.

**Theorem 1.1 (Weighted decomposition by pivot and cut).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount.weighted_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount.weighted_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a nonempty alphabet with distinct entries and any weight function from natural numbers to an additive commutative monoid, sum the weights of the lengths after the last first occurrence over doubled nonnesting words avoiding 1322. This sum equals the sum over pivots of two contributions. Type I ranges over upper and lower words and cuts at most the lower length following every lower first occurrence, with weight at lower length minus cut plus one. Type II ranges over upper words and cuts strictly below the upper length following every upper first occurrence, with weight at upper length minus cut plus lower alphabet size plus one, multiplied by the Catalan number of the lower alphabet size.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount.weighted_decomposition`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan](../ArrowThirtyTwoOneThreeCatalan.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal](NonnestingOneThreeTwoTwoTerminal.md)
