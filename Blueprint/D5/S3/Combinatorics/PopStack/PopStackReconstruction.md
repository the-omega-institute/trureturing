# Recovering a skeleton from a consecutive-value block

## Abstract

Let a permutation be written as a prefix, a nonempty block of consecutive values, and a suffix. There are a permutation skeleton and a standardized block whose inflation recovers the original permutation; their lengths are respectively the prefix length plus one plus the suffix length, and the block length. If every proper nontrivial interval of the original permutation is contained in that block, then the skeleton occurs in the original permutation and is simple. If the original permutation also belongs to C, so does the skeleton.

**Theorem 1.1 (Recovering a skeleton from a consecutive-value block).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackReconstruction.reconstruct_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackReconstruction.reconstruct_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let a permutation be written as a prefix, a nonempty block of consecutive values, and a suffix. There are a permutation skeleton and a standardized block whose inflation recovers the original permutation; their lengths are respectively the prefix length plus one plus the suffix length, and the block length. If every proper nontrivial interval of the original permutation is contained in that block, then the skeleton occurs in the original permutation and is simple. If the original permutation also belongs to C, so does the skeleton.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackReconstruction.reconstruct_interval`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackInflation](PopStackInflation.md)
