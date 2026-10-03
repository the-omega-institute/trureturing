# Rotation Blocks for 201 and 210 Avoidance

## Abstract

Distinct-entry words avoiding 201 and 210 have a unique decomposition into rotated increasing blocks.

**Theorem 1.1 (Splitting at the minimum).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.minimum_rotation_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.minimum_rotation_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let a word have pairwise distinct entries and be written as a prefix, its minimum entry, and a suffix. It avoids 201 and 210 if and only if the prefix is strictly increasing, every prefix entry is less than every suffix entry and the suffix avoids 201 and 210.

**Theorem 1.2 (Unique rotated-block decomposition).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.rotation_blocks_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.rotation_blocks_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

A word with pairwise distinct entries avoids 201 and 210 if and only if there is a unique list of nonempty blocks whose concatenation is strictly increasing and such that rotating each block by moving its first entry to the end and concatenating the rotated blocks gives the word. The empty word corresponds to the empty list of blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.minimum_rotation_split`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.rotation_blocks_unique`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix](InversionSeq152Prefix.md)
