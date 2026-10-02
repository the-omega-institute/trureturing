# The alternating prefix before the minimum

## Abstract

Let p be a permutation of size n at least four with maximum second, and write a for its first entry. In the suffix after its first two entries, assume values above a decrease and no value below a has both a smaller and a larger such value later. If adjacent entries never have consecutive values and the minimum has zero-based position k, then every entry before k is prescribed: at even position i it equals a minus i/2, and at odd position i it equals n minus floor(i/2).

**Theorem 1.1 (The alternating prefix before the minimum).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix.maximum_second_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix.maximum_second_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size n at least four with maximum second, and write a for its first entry. In the suffix after its first two entries, assume values above a decrease and no value below a has both a smaller and a larger such value later. If adjacent entries never have consecutive values and the minimum has zero-based position k, then every entry before k is prescribed: at even position i it equals a minus i/2, and at odd position i it equals n minus floor(i/2).

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix.maximum_second_prefix`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumShape](PopStackMaximumShape.md)
