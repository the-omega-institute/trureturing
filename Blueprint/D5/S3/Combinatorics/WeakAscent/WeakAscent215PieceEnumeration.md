# Enumeration of Original Pieces

## Abstract

A decreasing subset of original sites and an ordered list of pure histories enumerate the original pieces.

**Theorem 1.1 (Original pieces as subsets and lists).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration.original_piece_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration.original_piece_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For every gap g, original pieces have strictly decreasing cut sites and one more pure piece than cut sites. For either Boolean value of the old mark, the replay length equals the number of cut sites plus the sum of the pure piece lengths, and its expenditure equals the sum of their expenditures. There is a bijection from original pieces of gap g to pairs consisting of a subset S of the sites below g and an ordered list of cardinality S plus one pure histories; it sends the cut sites to S and preserves the ordered pure pieces.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration.original_piece_enumeration`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces](WeakAscent215Pieces.md)
