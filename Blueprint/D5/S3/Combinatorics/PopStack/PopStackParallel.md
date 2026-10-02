# Simplicity of the parallel family

## Abstract

For h at least one, P(h) is a simple permutation of the integers from one through 2h and belongs to both D and C.

**Definition 1.1 (Two alternating decreasing chains).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackParallel.P`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackParallel.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For each nonnegative h, P(h) has length 2h. At zero-based even position i its entry is h minus i/2, and at odd position i its entry is 2h minus floor(i/2). Thus the two decreasing value chains alternate.

**Theorem 1.2 (Simplicity of the parallel family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackParallel.parallel_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackParallel.parallel_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For h at least one, P(h) is a simple permutation of the integers from one through 2h and belongs to both D and C.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackParallel.P`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackParallel.parallel_simple`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackChains](PopStackChains.md)
