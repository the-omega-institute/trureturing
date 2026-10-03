# The Fibonacci enumeration

## Abstract

The numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two. For every n at least three, the number of simple permutations of size n sortable by two parallel pop stacks with bypass is F_(2n-5) minus the remainder of n on division by two, where F_0 = 0 and F_1 = 1.

**Theorem 1.1 (The Fibonacci enumeration).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackSimple.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackSimple.result` (`✓ std3`). ∎

*Resolves.* `Problems/cioni-ferrari-smith-pop-stack-simple` (proved) by `D5/S3/Combinatorics/PopStack/PopStackSimple.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cioni-ferrari-smith-pop-stack-simple","declaration_gid":"D5/S3/Combinatorics/PopStack/PopStackSimple.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two. For every n at least three, the number of simple permutations of size n sortable by two parallel pop stacks with bypass is F_(2n-5) minus the remainder of n on division by two, where F_0 = 0 and F_1 = 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackSimple.result`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackContinuationAvoidance](PopStackContinuationAvoidance.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackContinuationReflection](PopStackContinuationReflection.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackThirdEquivalence](PopStackThirdEquivalence.md)
