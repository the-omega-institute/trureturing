# An exhausted lower chain

## Abstract

Let p have size n at least four and maximum second. Assume the upper values after its first two entries decrease, no lower value has both a smaller and a larger lower value later, and adjacent values are never consecutive, where upper and lower are relative to its first entry. If the minimum has even zero-based position k at least two and the first entry equals k/2 + 1, then either n = k + 1 and p = E(k/2), or n = k + 2 and p = P(k/2 + 1).

**Theorem 1.1 (An exhausted lower chain).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal.exhausted_lower_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal.exhausted_lower_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p have size n at least four and maximum second. Assume the upper values after its first two entries decrease, no lower value has both a smaller and a larger lower value later, and adjacent values are never consecutive, where upper and lower are relative to its first entry. If the minimum has even zero-based position k at least two and the first entry equals k/2 + 1, then either n = k + 1 and p = E(k/2), or n = k + 2 and p = P(k/2 + 1).

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal.exhausted_lower_prefix`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackExtra](PopStackExtra.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix](PopStackMaximumPrefix.md)
