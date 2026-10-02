# Pure Histories and Original Pieces

## Abstract

Pure histories and recursive cuts describe the pieces below a newly created record.

**Definition 1.1 (Pure histories).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.PureHistory`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.PureHistory` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

A pure history is a list of pure steps admitting a run from the empty Boolean stack to some terminal stack.

**Definition 1.2 (Recursive original pieces).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.OriginalPieces`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.OriginalPieces` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a nonnegative gap g, original pieces consist either of a final pure history or of a cut at a site s below g, a pure history preceding that cut, and original pieces with the smaller gap s.

**Definition 1.3 (Replaying original pieces).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.replay`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.replay` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For gap g and an old mark e, replay shifts the descent sites of the first pure history by g plus one when e is true and by g otherwise. A final piece ends there. A cut at site s appends a descent to s and continues by replaying the remaining pieces with old mark false.

**Definition 1.4 (The cut-site list).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.sites`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.sites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The site list is empty for a final piece. A cut contributes its site followed by the sites of the remaining pieces, viewed as sites below the original gap.

**Definition 1.5 (The ordered pure pieces).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.pieces`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.pieces` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The pure-piece list consists of the terminal history in the final case. At a cut it consists of the history preceding the cut followed by the pure pieces of the remaining collection.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.OriginalPieces`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.PureHistory`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.pieces`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.replay`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.sites`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure](WeakAscent215Pure.md)
