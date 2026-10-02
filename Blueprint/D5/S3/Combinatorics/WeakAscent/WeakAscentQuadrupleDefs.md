# Weak Ascent Sequences Avoiding Four Patterns

## Abstract

Two quadruples of length-three patterns define the weak ascent sequence classes of Class 215.

**Definition 1.1 (Avoiders of a pattern family).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a nonnegative integer n and a list B of patterns, the avoiders are the weak ascent sequences of length n containing no pattern in B. Containment preserves both equalities and strict relative order among the selected entries.

**Definition 1.2 (The Class 215 equinumerosity assertion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.claim215`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.claim215` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For every nonnegative integer n, the number of weak ascent sequences of length n avoiding 100, 101, 110 and 201 equals the number avoiding 021, 101, 201 and 210. The same patterns written with letters starting at one are respectively 211, 212, 221, 312 and 132, 212, 312, 321.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.claim215`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](../Nonnesting/NonnestingDefs.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentDefs](WeakAscentDefs.md)
