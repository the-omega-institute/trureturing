# Schroeder Enumeration of the Sorting Class

## Abstract

The sorting class of the stack avoiding 23-1 is enumerated by the large Schroeder numbers.

**Definition 1.1 (Levels of the labelled tree).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackSort.labelledLevel`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackSort.labelledLevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The labelled tree has a single root of label two. A vertex of label k has k children indexed from zero through k minus one. Its child of index zero has label k plus one; a child of positive index i has label i plus two. A level consists of all vertices at its depth together with their labels.

**Theorem 1.2 (The Schroeder enumeration).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackSort.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackSort.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhao-vincular-stack-sorting-schroeder` (proved) by `D5/S3/Combinatorics/VincularStack/VincularStackSort.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhao-vincular-stack-sorting-schroeder","declaration_gid":"D5/S3/Combinatorics/VincularStack/VincularStackSort.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every positive n, the number of permutations of one through n whose image under the right-greedy stack map avoiding 23-1 avoids the classical pattern 231 equals the large Schroeder number of index n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackSort.labelledLevel`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackSort.result`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackTree](VincularStackTree.md)
