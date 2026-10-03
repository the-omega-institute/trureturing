# The Shieh-Yang-Yu 12-Dot Machine

## Abstract

Peak-run reversal followed by West's stack map defines the 12-dot machine and its sortable permutations.

**Definition 1.1 (Peak runs).**

Lean statement: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.peakRuns`

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.peakRuns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For a word of natural numbers, the empty word has no peak runs. For a nonempty word beginning with v, the first run consists of v followed by the longest initial segment of the remaining word whose entries are at most v. The remaining runs are obtained by applying the same rule to the remaining suffix. On permutations, each run begins at a left-to-right maximum and ends immediately before the next left-to-right maximum, as in Section 2 of the cited paper.

**Definition 1.2 (Reverse each peak run).**

Lean statement: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.s12`

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.s12` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

The map s12 reverses each peak run and concatenates the reversed runs in their original order. Proposition 3.1 of the cited paper identifies this operation on permutations with the stack map avoiding the dotted pattern 12-dot. Peak-run reversal is the definition of s12 for all words of natural numbers.

**Definition 1.3 (Machine-sortable permutations).**

Lean statement: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.sortable`

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.sortable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For a natural number n, sortable(n) is the set of permutations of the word [1,...,n] for which applying s12 and then West's stack map gives [1,...,n]. West's map pops the stack while its top is smaller than the next input, pushes that input otherwise, and flushes the remaining stack when the input is empty. Sortability requires a single application of this composition.

**Definition 1.4 (The central binomial assertion).**

Lean statement: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.claim`

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

The proposition claim states that, for every natural number n at least one, the number of elements of sortable(n) is the binomial coefficient choosing n minus one from 2n minus two. This is Conjecture 6.1 of the cited paper, with the first stack map expressed by peak-run reversal.

## References

- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.claim`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.peakRuns`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.s12`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.sortable`
- Dependency: [D5/S1/Words/Patterns/ShiehYangYuMachineConvergence](ShiehYangYuMachineConvergence.md)
