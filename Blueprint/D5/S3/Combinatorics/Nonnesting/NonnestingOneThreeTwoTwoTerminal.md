# Unique Terminal Factorization

## Abstract

The last first occurrence determines a unique terminal insertion of one of two types.

**Theorem 1.1 (Two-type terminal factorization).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal.terminal_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal.terminal_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let a word have exactly two copies of each of its letters, and let the pivot have the last first occurrence. The word avoids 1221, 2112, and 1322 if and only if its upper and lower subsequences avoid all three patterns and it has unique type I or type II parameters. In type I, the cut is at most the lower length and follows every lower first occurrence. In type II, the lower subsequence consists of two copies of an order with distinct entries, and the cut is strictly below the upper length and follows every upper first occurrence. The length after the first pivot is lower length minus cut plus one in type I, and upper length minus cut plus lower order length plus one in type II.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal.terminal_factorization`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition](NonnestingOneThreeTwoTwoPartition.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting](NonnestingOneThreeTwoTwoTypeIINesting.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting](NonnestingOneThreeTwoTwoTypeINesting.md)
