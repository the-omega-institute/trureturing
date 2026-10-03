# Stack Sorting and Peak-Run Structure

## Abstract

West's stack map sorts distinct words exactly when they avoid 231, and peak runs preserve the entries of a word.

**Theorem 1.1 (West's sorting criterion).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.west_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.west_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every word of pairwise distinct natural numbers, the output of West's stack map is strictly increasing if and only if the word avoids the pattern 231. An occurrence of 231 consists of three entries in their original order whose third entry is smaller than the first and whose first entry is smaller than the second.

**Theorem 1.2 (Structure of peak runs).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.peak_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.peak_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every word of natural numbers, concatenating its peak runs recovers the word, and s12 produces a permutation of that word. Each peak run is nonempty and has a leading entry at least as large as every entry in its remaining body. For any two peak runs in their original order, every entry of the earlier run is strictly smaller than the leading entry of the later run.

## References

- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.peak_structure`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest.west_criterion`
- Dependency: [D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs](../../../S1/Words/Patterns/ShiehYangYuTwelveDotDefs.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenNineClassicalSplit](../Fishburn/FishburnTenNineClassicalSplit.md)
