# Pattern Occurrences and Stack Invariants

## Abstract

Adjacent pattern occurrences and order preservation control the three stack maps.

**Theorem 1.1 (An adjacent descent in a 312 occurrence).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.classical_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.classical_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A word with distinct entries contains the classical pattern 312 if and only if it contains 31-2 with the entries playing 3 and 1 adjacent.

**Theorem 1.2 (Preservation under insertion).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.push_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.push_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For any pair of adjacency flags, if the initial stack avoids the specified form of 312, right-greedy insertion leaves a stack avoiding that form. The concatenation of the popped entries and the remaining stack is a permutation of the inserted entry followed by the original stack, and contains the original stack as a subsequence.

**Theorem 1.3 (Preservation under processing).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.process_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.process_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For any pair of adjacency flags, processing any input from a stack avoiding the specified form of 312 produces a permutation of the input concatenated with that stack. The original stack occurs as a subsequence of the output.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.classical_adjacent`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.process_preserves`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.push_preserves`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs](VincularStackThreeDefs.md)
