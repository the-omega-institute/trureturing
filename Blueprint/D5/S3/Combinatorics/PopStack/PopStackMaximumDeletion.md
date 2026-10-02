# Deletion before the minimum when the maximum is second

## Abstract

Let p be a permutation of size at least five with maximum second. In the suffix after its first two entries, values above the first entry decrease, and no value below the first entry has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least three, and p is neither P(floor(n/2)) nor E(floor(n/2)), where n is its length. Delete the entry immediately before the minimum and standardize. The predecessor is a simple permutation in C with maximum second and minimum at position k minus one, and remains outside those two families. Inserting before its minimum the rank prescribed by the parity of that position recovers p.

**Theorem 1.1 (Deletion before the minimum when the maximum is second).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion.maximum_second_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion.maximum_second_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size at least five with maximum second. In the suffix after its first two entries, values above the first entry decrease, and no value below the first entry has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least three, and p is neither P(floor(n/2)) nor E(floor(n/2)), where n is its length. Delete the entry immediately before the minimum and standardize. The predecessor is a simple permutation in C with maximum second and minimum at position k minus one, and remains outside those two families. Inserting before its minimum the rank prescribed by the parity of that position recovers p.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion.maximum_second_deletion`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals](PopStackMaximumIntervals.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal](PopStackMaximumTerminal.md)
