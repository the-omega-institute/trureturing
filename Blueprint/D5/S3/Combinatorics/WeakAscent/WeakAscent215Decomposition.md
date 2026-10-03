# Decomposition at the First Record

## Abstract

The first record splits a nonempty pure history into a gap, descending sites and smaller pure histories.

**Theorem 1.1 (First-record decomposition and its series identity).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition.first_record_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition.first_record_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Nonempty pure histories are in bijection with triples consisting of a nonnegative gap g, a subset S of the sites from zero through g minus one, and an ordered list of cardinality S plus one pure histories. The sites occur in decreasing order. Reconstruction starts with a record of gap g and then replays the corresponding pieces above an old entry. Its length is one plus the cardinality of S plus the sum of the piece lengths, and its expenditure is g plus the sum of the piece expenditures. If P(z,x) counts pure histories by expenditure z and length x, then P + z(1 + xP) = 1 + xP + z(1 + xP)P.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition.first_record_decomposition`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration](WeakAscent215PieceEnumeration.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Products](WeakAscent215Products.md)
