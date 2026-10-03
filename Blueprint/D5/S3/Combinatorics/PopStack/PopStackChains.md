# A cut into decreasing chains

## Abstract

For a word with distinct entries, membership in D is equivalent to the existence of a value cut such that entries on each side of the cut occur in decreasing order. Every such word belongs to C.

**Definition 1.1 (The two-chain class).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackChains.InD`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackChains.InD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The class D consists of words avoiding the classical patterns 123, 3142 and 3412.

**Theorem 1.2 (A cut into decreasing chains).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackChains.two_decreasing_chains`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackChains.two_decreasing_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For a word with distinct entries, membership in D is equivalent to the existence of a value cut such that entries on each side of the cut occur in decreasing order. Every such word belongs to C.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackChains.InD`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackChains.two_decreasing_chains`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackDefs](PopStackDefs.md)
