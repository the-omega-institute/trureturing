# Intervals when the maximum is second

## Abstract

Let p be a permutation of size at least four with maximum second. Suppose that, after its first two entries, the values above its first entry decrease and no value below its first entry has both a smaller and a larger such value later. Then p belongs to C. It has no adjacent entries with consecutive values if and only if it is simple or equals E(h) for some h at least two.

**Theorem 1.1 (Intervals when the maximum is second).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals.maximum_second_intervals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals.maximum_second_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size at least four with maximum second. Suppose that, after its first two entries, the values above its first entry decrease and no value below its first entry has both a smaller and a larger such value later. Then p belongs to C. It has no adjacent entries with consecutive values if and only if it is simple or equals E(h) for some h at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals.maximum_second_intervals`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackExtra](PopStackExtra.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix](PopStackMaximumPrefix.md)
