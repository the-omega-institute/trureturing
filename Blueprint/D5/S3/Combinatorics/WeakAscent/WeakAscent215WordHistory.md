# Active Values and Occurrence Marks

## Abstract

Increasing active values and their occurrence marks associate a Boolean stack with a word.

**Definition 1.1 (The increasing active-value list).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeValues`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a word w, the active-value list consists, in increasing order, of the nonnegative values at most its maximum that can be appended to give a weak ascent sequence of length one more avoiding 100, 101, 110 and 201. The maximum of the empty word is taken to be zero.

**Definition 1.2 (Occurrence marks of active values).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeMarks`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeMarks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The active-mark list replaces each entry of the increasing active-value list by true when that value occurs in the original word and by false otherwise.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeMarks`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.activeValues`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal](WeakAscent215Renewal.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Sites](WeakAscent215Sites.md)
