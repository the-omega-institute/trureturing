# Reverse vertical continuation

## Abstract

For a word p of length n, undoV(p) equals P(floor(n/2)) if p = E(floor(n/2)), and equals E(floor(n/2)-1) if p = P(floor(n/2)). Otherwise, if the second entry is below n, delete the first entry and decrease each remaining value greater than it. In the remaining case delete the entry immediately before the minimum and decrease each remaining value larger than the deleted entry. Subtraction is truncated at zero.

**Definition 1.1 (The augmented simple class).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.augmented`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.augmented` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For each nonnegative n, augmented(n) consists of the simple permutations of size n in C, together with E(floor(n/2)) when n is odd and at least three.

**Definition 1.2 (Vertical continuation).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.V`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.V` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For a word p of length n, V(p) equals E(floor(n/2)) if p = P(floor(n/2)). If p = E(floor(n/2)), insert the rank floor((n+3)/2) at the end after increasing every value at least that rank. Otherwise, if the second entry is less than n, use W(p). In the remaining case let k be the zero-based position of one and choose rank a minus k/2 plus one when k is even, or n minus (k-1)/2 plus one when k is odd, where a is the first entry. Increase every value at least that rank and insert it immediately before the minimum.

**Definition 1.3 (Reverse vertical continuation).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.undoV`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.undoV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For a word p of length n, undoV(p) equals P(floor(n/2)) if p = E(floor(n/2)), and equals E(floor(n/2)-1) if p = P(floor(n/2)). Otherwise, if the second entry is below n, delete the first entry and decrease each remaining value greater than it. In the remaining case delete the entry immediately before the minimum and decrease each remaining value larger than the deleted entry. Subtraction is truncated at zero.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.V`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.augmented`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.undoV`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackContinuation](PopStackContinuation.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion](PopStackMaximumDeletion.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion](PopStackMaximumInsertion.md)
