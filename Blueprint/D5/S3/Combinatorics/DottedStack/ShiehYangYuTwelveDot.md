# The Central Binomial Count for the 12-Dot Machine

## Abstract

The 12-dot machine sorts a central binomial number of permutations of each positive size.

**Theorem 1.1 (Count the machine-sortable permutations).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every natural number n at least one, exactly the binomial coefficient choosing n minus one from 2n minus two permutations of [1,...,n] are sent to [1,...,n] by peak-run reversal followed by West's stack map. Peak-run reversal is the closed form in Proposition 3.1 of the cited paper, so this count is the assertion of Conjecture 6.1. West's criterion reduces sortability to 231 avoidance after peak-run reversal. The fibres give two choices per record of an avoiding permutation of size n minus one. The permutation-to-Dyck-path bijection carries the number of records to the number of primitive excursions. Coloring and reflecting these excursions gives all balanced bridges with n minus one up steps and n minus one down steps, counted by their up-step positions.

## References

- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.result`
- Dependency: [D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths](ShiehYangYuTwelveDotPaths.md)
