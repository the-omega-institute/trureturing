# Endpoints of Pure Histories

## Abstract

Terminal records and old entries describe the endpoints of pure histories.

**Definition 1.1 (Old entries in the terminal stack).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.oldCount`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.oldCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The old-entry count of a pure history is the number of true marks in a terminal stack obtained by running that history from the empty stack.

**Definition 1.2 (The final pure piece).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.finalPiece`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.finalPiece` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The final piece of a recursive collection of original pieces is its terminal pure history, obtained by following the successive cuts to the final case.

**Theorem 1.3 (Histories ending in a record).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.record_endings`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.record_endings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Pure histories whose last step is a record are in bijection with pairs consisting of a pure history and a nonnegative gap. Reconstruction appends a record of that gap, increasing the length by one and the expenditure by the gap.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.finalPiece`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.oldCount`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.record_endings`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition](WeakAscent215Decomposition.md)
