# Three Stacks Avoiding Patterns of Order Three

## Abstract

The stacks avoiding 312, 31-2 and 3-12 define three sorting classes and their common-output assertion.

**Definition 1.1 (The three forms of 312).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Contains312`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Contains312` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A stack word, read from top to bottom, contains 312 when three entries at strictly increasing positions have the second entry less than the third and the third less than the first. The flag adj31 requires the first two positions to be adjacent, giving 31-2; the flag adj12 requires the last two positions to be adjacent, giving 3-12. When both flags are false, there is no adjacency requirement.

**Definition 1.2 (Decidable pattern containment).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.instDecidableContains312`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.instDecidableContains312` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Containment of each specified form of 312 in a finite stack word is decidable by testing all bounded triples of positions, their value inequalities and the required adjacencies.

**Definition 1.3 (Right-greedy insertion).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Push`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Push` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

To insert an entry, push it onto the stack if the resulting stack avoids the specified form of 312. Otherwise pop the top entry and retry. The operation returns the popped entries in their output order and the remaining stack, read from top to bottom.

**Definition 1.4 (Processing a word).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Process`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Process` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Starting from a given stack, process the input word from left to right by right-greedy insertion. Concatenate the popped entries in order and then the final stack read from top to bottom.

**Definition 1.5 (The three stack maps).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.SC`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.SC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The map SC sends a word to the output obtained by processing it from an empty stack. The flag pairs false and false, true and false, and false and true specify avoidance of 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent, respectively.

**Definition 1.6 (The sorting classes).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.sortable`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.sortable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every nonnegative n and each pair of adjacency flags, the sorting class consists of permutations of the integers from one through n whose image under the corresponding stack map avoids the classical pattern 231.

**Definition 1.7 (Equal sorting classes and common outputs).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.claim`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every positive n, the sorting classes of the stacks avoiding 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent are equal. On every permutation in the common sorting class, the three stack maps have equal outputs.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Contains312`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Process`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.Push`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.SC`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.instDecidableContains312`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.sortable`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackDefs](VincularStackDefs.md)
