# Position Bounds for Rotated Blocks

## Abstract

Position bounds on rotated blocks separate into bounds on the sorted word and on each block tail.

**Theorem 1.1 (Bounds before and after rotation).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds.rotated_suffix_bounds_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds.rotated_suffix_bounds_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let a list of nonempty blocks have strictly increasing concatenation, and let b be nonnegative. Rotate each block by moving its first entry to the end. Every entry of the resulting concatenation is at most b plus its position if and only if every entry of the original concatenation satisfies that bound and every entry at position j in a block tail is at most b plus the total length of preceding blocks plus j. All positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds.rotated_suffix_bounds_iff`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation](InversionSeq152Rotation.md)
