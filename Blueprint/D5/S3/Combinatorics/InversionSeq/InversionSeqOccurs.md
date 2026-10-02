# Occurrences of Length-Three Patterns

## Abstract

Occurrences of length-three patterns are characterized by three positions and their pairwise comparisons.

**Theorem 1.1 (Three-position characterization).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs.occurs_three_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs.occurs_three_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let a, b and c be positive integers containing every rank from one through their maximum. The pattern with entries a, b and c occurs in a word if and only if there are three strictly increasing positions in the word whose entries have exactly the same pairwise strict inequalities and equalities as a, b and c.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs.occurs_three_iff`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqDefs](InversionSeqDefs.md)
