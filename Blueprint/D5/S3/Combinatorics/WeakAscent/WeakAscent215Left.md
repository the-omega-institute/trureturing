# Appending to the First Avoidance Class

## Abstract

Repeated values and inversion intervals characterize appending in the first Class 215 family.

**Definition 1.1 (The largest repeated value).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.repeatedThreshold`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.repeatedThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The repeated threshold of a word is its greatest value occurring at least twice, or zero when there is no repeated value.

**Theorem 1.2 (The criterion for appending a letter).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.left_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.left_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Let w be a nonempty weak ascent sequence avoiding 100, 101, 110 and 201, and let a be a nonnegative integer. Appending a preserves this avoidance class exactly when a is at least the repeated threshold of w, is at most one plus the weak ascent count of w, and belongs to no closed interval from the lower value to the upper value of an inversion of w.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.left_append_iff`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.repeatedThreshold`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs](../InversionSeq/InversionSeqOccurs.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs](WeakAscentQuadrupleDefs.md)
