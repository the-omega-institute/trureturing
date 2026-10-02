# Intervals and simplicity in the terminal families

## Abstract

For n at least four, R(n) is a permutation of size n in C ending in its minimum. Its proper nontrivial intervals are exactly the prefix of length n minus one with values from two through n and, when n is even, the second and third entries with values n minus one and n. Moreover, Y(n+1) is a simple permutation of size n + 1 in C.

**Definition 1.1 (Minimum insertion in the terminal-gap family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.Y`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.Y` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For each nonnegative n, Y(n) is obtained from R(n-1) by increasing every entry by one and inserting the minimum one at zero-based position two. Subtraction is truncated at zero.

**Theorem 1.2 (Intervals and simplicity in the terminal families).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.terminal_family_intervals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.terminal_family_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For n at least four, R(n) is a permutation of size n in C ending in its minimum. Its proper nontrivial intervals are exactly the prefix of length n minus one with values from two through n and, when n is even, the second and third entries with values n minus one and n. Moreover, Y(n+1) is a simple permutation of size n + 1 in C.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.Y`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.terminal_family_intervals`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMinimum](PopStackMinimum.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackTerminalGap](PopStackTerminalGap.md)
