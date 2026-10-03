# Fibres of Peak-Run Reversal

## Abstract

Preimages of peak-run reversal correspond to ordered block decompositions, and record values specify possible cuts.

**Definition 1.1 (A block description of each fibre).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.fibre_equiv`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.fibre_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every output word, fibre_equiv is a bijection between inputs whose s12 image is that output and lists of blocks concatenating to the output with the following properties. Each reversed block is nonempty, and every entry after its leader is at most that leader. For any two reversed blocks in their original order, every entry of the earlier block is strictly smaller than the leader of the later block. The forward map reverses each peak run of the input. The inverse reverses each output block and concatenates them.

**Definition 1.2 (Record values).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.recordCuts`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.recordCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every word of natural numbers, recordCuts is the finite set of values in the word whose first occurrence is strictly larger than every preceding entry. The first entry has no preceding entries and is therefore a record. The set consists of values, rather than their positions; for permutations these values correspond uniquely to the left-to-right maximum positions.

## References

- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.fibre_equiv`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.recordCuts`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](../ArrowWilfDefs.md)
- Dependency: [D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest](ShiehYangYuTwelveDotWest.md)
