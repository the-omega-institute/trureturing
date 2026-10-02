# Deleting a minimum in the second position

## Abstract

Let q be a permutation in C of size at least four with minimum in its second position, and let p be obtained by deleting that minimum and subtracting one from every remaining entry. Then p is a permutation in C, and shifting its values up by one and reinserting the minimum recovers q. The permutation q is simple if and only if p is simple with minimum not in the second position, or p is the first-entry decreasing inflation of a simple skeleton in C of size at least four, or p equals B at its size.

**Theorem 1.1 (Deleting a minimum in the second position).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDecomposition.minimum_two_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackDecomposition.minimum_two_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let q be a permutation in C of size at least four with minimum in its second position, and let p be obtained by deleting that minimum and subtracting one from every remaining entry. Then p is a permutation in C, and shifting its values up by one and reinserting the minimum recovers q. The permutation q is simple if and only if p is simple with minimum not in the second position, or p is the first-entry decreasing inflation of a simple skeleton in C of size at least four, or p equals B at its size.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDecomposition.minimum_two_decomposition`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackCrossing](PopStackCrossing.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackFamilies](PopStackFamilies.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMinimum](PopStackMinimum.md)
