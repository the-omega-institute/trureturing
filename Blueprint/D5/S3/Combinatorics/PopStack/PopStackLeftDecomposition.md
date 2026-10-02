# Simplicity after prepending two

## Abstract

Let p be a permutation of size at least three with minimum in its second position. Prepend two after increasing every other value than one by one. The result is simple if and only if every proper nontrivial interval of p is its second and third entries with values one and two. The result is both simple and in C if and only if exactly one of the following holds: p itself is simple and in C; or p is the second-entry inflation by 12 of a unique simple skeleton in C whose minimum is second and whose length is two or at least four.

**Theorem 1.1 (Simplicity after prepending two).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition.prepend_two_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition.prepend_two_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size at least three with minimum in its second position. Prepend two after increasing every other value than one by one. The result is simple if and only if every proper nontrivial interval of p is its second and third entries with values one and two. The result is both simple and in C if and only if exactly one of the following holds: p itself is simple and in C; or p is the second-entry inflation by 12 of a unique simple skeleton in C whose minimum is second and whose length is two or at least four.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition.prepend_two_decomposition`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackLeft](PopStackLeft.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackReconstruction](PopStackReconstruction.md)
