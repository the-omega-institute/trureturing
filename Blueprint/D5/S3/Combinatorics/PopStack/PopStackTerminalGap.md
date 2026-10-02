# Classification of a terminal crossing gap

## Abstract

Let p be a permutation of size n at least four in D ending with its minimum. Suppose every proper nontrivial interval crosses the gap of zero-based index two strictly and has minimum value at least two. Then p = R(n).

**Definition 1.1 (The terminal-gap family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.R`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.R` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For odd n, R(n) equals E(floor(n/2)). For even n, its first two entries are n/2 and n; at later even zero-based position i its entry is n minus i/2, and at later odd position i its entry is n/2 minus floor(i/2).

**Theorem 1.2 (Classification of a terminal crossing gap).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.terminal_gap_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.terminal_gap_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size n at least four in D ending with its minimum. Suppose every proper nontrivial interval crosses the gap of zero-based index two strictly and has minimum value at least two. Then p = R(n).

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.R`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackTerminalGap.terminal_gap_classification`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackExtra](PopStackExtra.md)
