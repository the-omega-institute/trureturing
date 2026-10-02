# Equal Sorting Classes and Outputs

## Abstract

The stacks avoiding 312, 31-2 and 3-12 sort the same permutations and agree on their outputs.

**Theorem 1.1 (Equal sorting classes and outputs).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThree.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhao-vincular-stack-three-sorting-classes` (proved) by `D5/S3/Combinatorics/VincularStack/VincularStackThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhao-vincular-stack-three-sorting-classes","declaration_gid":"D5/S3/Combinatorics/VincularStack/VincularStackThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every positive n, the sorting classes of the stacks avoiding 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent are equal. On every permutation in the common sorting class, the three stack maps have equal outputs.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThree.result`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence](VincularStackThreeDivergence.md)
