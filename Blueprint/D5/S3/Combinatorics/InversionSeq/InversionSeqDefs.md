# Inversion Sequences and Pattern Avoidance

## Abstract

Inversion sequences and pattern avoidance define the equinumerosity assertions for Classes 152 and 207.

**Definition 1.1 (Inversion sequences).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.IsInversionSeq`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.IsInversionSeq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

A word of nonnegative integers is an inversion sequence when its entry at each position i, numbered from zero, is at most i. The empty word is included.

**Definition 1.2 (Avoiders of a fixed length).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For a nonnegative integer n and a list B of patterns, the set I_n(B) consists of inversion sequences of length n avoiding every pattern in B. A pattern occurrence preserves both equality and relative order of entries.

**Definition 1.3 (The Class 152 assertion).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim152`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim152` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The Class 152 assertion is the proposition that, for every nonnegative n, the number of inversion sequences of length n avoiding 010, 100, 102 and 210 equals the number avoiding 011, 201 and 210.

**Definition 1.4 (The Class 207 assertion).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim207`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim207` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The Class 207 assertion is the proposition that, for every nonnegative n, the number of inversion sequences of length n avoiding 100, 101, 110 and 201 equals the number avoiding 101, 110, 120 and 210.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.IsInversionSeq`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim152`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.claim207`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](../Nonnesting/NonnestingDefs.md)
