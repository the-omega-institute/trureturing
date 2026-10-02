# The Stack Avoiding 23-1

## Abstract

The right-greedy stack avoiding 23-1 defines a sorting class and its Schroeder enumeration assertion.

**Definition 1.1 (The vincular pattern 23-1).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.ContainsV`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.ContainsV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A stack word, read from top to bottom, contains 23-1 when two adjacent entries are increasing and a later entry is less than the first of those two entries.

**Definition 1.2 (Decidable pattern containment).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.instDecidableContainsV`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.instDecidableContainsV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Containment of 23-1 in a finite stack word is decidable by testing all bounded choices of the adjacent positions and the later position.

**Definition 1.3 (Right-greedy insertion).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Push`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Push` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

To insert an entry, push it onto the stack if the resulting stack avoids 23-1. Otherwise pop the top entry and retry. The operation returns the popped entries in their output order and the remaining stack, read from top to bottom.

**Definition 1.4 (Processing a word).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Process`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Process` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Starting from a given stack, process the input word from left to right by right-greedy insertion. Concatenate the popped entries in order and then the final stack read from top to bottom.

**Definition 1.5 (The right-greedy stack map).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.SC`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.SC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The map SC sends a word to the output obtained by processing it from an empty stack with right-greedy insertion avoiding 23-1.

**Definition 1.6 (The classical pattern 231).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Contains231`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Contains231` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A word contains 231 when three entries at strictly increasing positions have the third entry less than the first and the first less than the second.

**Definition 1.7 (The sorting class).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.sortable`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.sortable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every nonnegative n, the sorting class consists of permutations of the integers from one through n whose image under SC avoids the classical pattern 231.

**Definition 1.8 (The Schroeder enumeration assertion).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.claim`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every positive n, the number of permutations of one through n whose image under SC avoids 231 equals the large Schroeder number of index n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Contains231`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.ContainsV`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Process`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.Push`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.SC`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.instDecidableContainsV`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackDefs.sortable`
