# Deleting the first entry of an ordinary continuation

## Abstract

Let q be a simple permutation in C whose minimum has position k at least three and whose second entry is below its maximum. Delete the first entry and decrease each remaining value larger than the deleted value. The resulting permutation p is simple, belongs to C, has its minimum at position k minus one, has its second entry below its maximum, and satisfies W(p) = q. Positions are numbered from zero.

**Theorem 1.1 (Deleting the first entry of an ordinary continuation).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackContinuationReflection.ordinary_continuation_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackContinuationReflection.ordinary_continuation_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let q be a simple permutation in C whose minimum has position k at least three and whose second entry is below its maximum. Delete the first entry and decrease each remaining value larger than the deleted value. The resulting permutation p is simple, belongs to C, has its minimum at position k minus one, has its second entry below its maximum, and satisfies W(p) = q. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackContinuationReflection.ordinary_continuation_inverse`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackContinuation](PopStackContinuation.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackReconstruction](PopStackReconstruction.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackThirdEntry](PopStackThirdEntry.md)
