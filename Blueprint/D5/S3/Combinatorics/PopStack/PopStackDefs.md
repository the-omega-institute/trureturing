# The Fibonacci enumeration assertion

## Abstract

The assertion is that the numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two, and that for every n at least three the number is F_(2n-5) minus the remainder of n on division by two. The Fibonacci sequence has F_0 = 0 and F_1 = 1.

**Definition 1.1 (Classical pattern containment).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.Occurs`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.Occurs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

A pattern occurs in a word when a subsequence of that word has the same relative order as the pattern.

**Definition 1.2 (The forbidden basis).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.basis`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.basis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The forbidden basis consists of 2341, 25314, 42513, 42531, 45213, 45231, 52314, 642135 and 642153.

**Definition 1.3 (The sortable class).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.InC`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.InC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

A word belongs to C when none of the patterns in the forbidden basis occurs in it.

**Definition 1.4 (Simple permutations).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.IsSimple`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.IsSimple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

A word is simple when no consecutive segment of length at least two and less than its total length has a set of consecutive values.

**Definition 1.5 (Simple sortable permutations of a fixed size).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.simples`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.simples` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For each nonnegative n, simples(n) is the set of permutations of the integers from one through n that belong to C and are simple.

**Definition 1.6 (The Fibonacci enumeration assertion).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackDefs.claim`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The assertion is that the numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two, and that for every n at least three the number is F_(2n-5) minus the remainder of n on division by two. The Fibonacci sequence has F_0 = 0 and F_1 = 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.InC`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.IsSimple`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.Occurs`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.basis`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackDefs.simples`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](../ArrowWilfDefs.md)
