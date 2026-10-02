# The unique proper interval of an odd extra

## Abstract

For h at least one, E(h) is a permutation of size 2h + 1 in C and is not simple. Its only proper nontrivial interval is its prefix of length 2h, whose values are the integers from two through 2h + 1.

**Definition 1.1 (The odd extra family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackExtra.E`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackExtra.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For each nonnegative h, E(h) is obtained by adding one to every entry of P(h) and appending the minimum one.

**Theorem 1.2 (The unique proper interval of an odd extra).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackExtra.odd_extra`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackExtra.odd_extra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For h at least one, E(h) is a permutation of size 2h + 1 in C and is not simple. Its only proper nontrivial interval is its prefix of length 2h, whose values are the integers from two through 2h + 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackExtra.E`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackExtra.odd_extra`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackParallel](PopStackParallel.md)
