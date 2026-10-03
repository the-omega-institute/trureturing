# Insertion before the minimum when the maximum is second

## Abstract

Let p be a permutation of size n at least four with maximum second. In the suffix after its first two entries, values above its first entry a decrease, and no value below a has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least two, and p is neither P(floor(n/2)) nor E(floor(n/2)). If k is even choose rank a minus k/2 plus one; otherwise choose rank n minus (k-1)/2 plus one. Increase all values at least that rank and insert it before the minimum. The result is a simple permutation in C with maximum second, minimum at position k + 1, and outside the same two families. Deleting the inserted entry and standardizing recovers p.

**Theorem 1.1 (Insertion before the minimum when the maximum is second).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion.maximum_second_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion.maximum_second_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size n at least four with maximum second. In the suffix after its first two entries, values above its first entry a decrease, and no value below a has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least two, and p is neither P(floor(n/2)) nor E(floor(n/2)). If k is even choose rank a minus k/2 plus one; otherwise choose rank n minus (k-1)/2 plus one. Increase all values at least that rank and insert it before the minimum. The result is a simple permutation in C with maximum second, minimum at position k + 1, and outside the same two families. Deleting the inserted entry and standardizing recovers p.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion.maximum_second_insertion`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals](PopStackMaximumIntervals.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal](PopStackMaximumTerminal.md)
