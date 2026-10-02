# Contracting the first two entries

## Abstract

The word deflateFirst(p) starts with the second entry of p and then contains the entries after its first two positions, each decreased by one precisely when it exceeds that second entry. An absent second entry is read as zero.

**Definition 1.1 (Contracting the first two entries).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackM3Disjoint.deflateFirst`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackM3Disjoint.deflateFirst` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The word deflateFirst(p) starts with the second entry of p and then contains the entries after its first two positions, each decreased by one precisely when it exceeds that second entry. An absent second entry is read as zero.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackM3Disjoint.deflateFirst`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackDecomposition](PopStackDecomposition.md)
