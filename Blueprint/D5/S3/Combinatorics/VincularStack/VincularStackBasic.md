# Stack Invariants and Maximum Insertion

## Abstract

Stack invariants determine the output position of a newly inserted maximum.

**Theorem 1.1 (Testing a proposed push).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_test`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Placing an entry before a stack with top t creates a 23-1 occurrence precisely when the original stack already contains 23-1, or the entry is less than t and some entry below t is less than the inserted entry.

**Theorem 1.2 (Preservation under insertion).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

If the initial stack avoids 23-1, right-greedy insertion leaves a stack avoiding 23-1. The concatenation of the popped entries and the remaining stack is a permutation of the inserted entry followed by the original stack, and contains the original stack as a subsequence.

**Theorem 1.3 (Retention of a minimum).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Suppose the stack avoids 23-1 and contains a minimum m, and the inserted entry is at least m. Then m remains in the stack after insertion, and every popped entry is strictly greater than m.

**Theorem 1.4 (Preservation under processing).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.process_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.process_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Processing any input from a stack avoiding 23-1 produces a permutation of the input concatenated with that stack. The original stack occurs as a subsequence of the output.

**Definition 1.5 (The state before the final drain).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A snapshot records the output already popped and the stack remaining after all input entries have been inserted, before draining the final stack.

**Theorem 1.6 (A minimum in the final stack).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Suppose the initial stack avoids 23-1 and m is a minimum of the input concatenated with the stack. The snapshot stack avoids 23-1 and contains m, every entry already popped is strictly greater than m, and the full output is the popped word concatenated with the snapshot stack.

**Theorem 1.7 (A protected bottom segment).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.protected_suffix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.protected_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Suppose a stack avoiding 23-1 is an upper segment followed by a bottom segment. If the upper segment contains m and every entry in both segments is at least m, processing any input leaves the bottom segment untouched: the full output equals the output from the upper segment alone followed by the bottom segment.

**Definition 1.8 (The output gap of a maximum).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.outputGap`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackBasic.outputGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Split an input into a front and a suffix. If the front is empty, its output gap is the suffix length. Otherwise take the snapshot of the front from an empty stack. If the suffix is empty, or the snapshot stack contains an entry less than the first suffix entry, the gap is the popped length. In the remaining case it is the total input length minus the snapshot stack length.

**Theorem 1.9 (Inserting a maximum in the output).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let M exceed every entry of a front concatenated with a suffix. Inserting M between those two words inserts M into their original SC output at the output gap of that split and leaves the other entries in their original order. If the front is nonempty, the gap is strictly less than the original input length.

**Definition 1.10 (Separating output cuts).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.separatingCut`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackBasic.separatingCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A gap in a word is a separating cut when every entry before the gap is strictly less than every entry at or after the gap.

**Theorem 1.11 (Avoidance after inserting a maximum).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a front concatenated with a back have distinct entries, all less than M. The word obtained by inserting M between them avoids 231 precisely when the original word avoids 231 and the cut between the front and back is separating.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_cut`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.maximum_insertion`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.outputGap`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.process_preserves`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.protected_suffix`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_minimum`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_preserves`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.push_test`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.separatingCut`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackBasic.snapshot_minimum`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackDefs](VincularStackDefs.md)
