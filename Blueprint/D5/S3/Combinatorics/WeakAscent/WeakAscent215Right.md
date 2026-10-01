# The Second Avoidance Class

## Abstract

The positive entries and intervening zeros characterize the second Class 215 family.

**Theorem 1.1 (An intrinsic avoidance criterion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.intrinsic_right_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.intrinsic_right_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a word of nonnegative integers whose entry at position zero is zero, using zero also for a missing entry, avoidance of 021, 101, 201 and 210 is equivalent to both of the following conditions. The positive entries in their original order are weakly increasing. Whenever a positive entry precedes a zero and that zero precedes a later entry, the first and last of these three entries are unequal. The empty word is included.

**Theorem 1.2 (Appending in the second class).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.right_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.right_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Let w be a nonempty weak ascent sequence avoiding 021, 101, 201 and 210. A nonnegative letter a can be appended while preserving this class exactly when a is at most one plus the weak ascent count of w and either a is zero, a is greater than the maximum of w, or a equals that maximum and the last entry of w is positive.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.intrinsic_right_iff`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.right_append_iff`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs](../InversionSeq/InversionSeqOccurs.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentGrowth](WeakAscentGrowth.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs](WeakAscentQuadrupleDefs.md)
