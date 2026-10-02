# Structure of the Left Avoidance Class

## Abstract

Avoidance of 010, 100, 102 and 210 is characterized by the structure at the first descent.

**Theorem 1.1 (Uniqueness after a larger entry).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.low_value_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.low_value_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

In a word avoiding 010 and 100, any entry preceded by a strictly larger entry occurs at exactly one position in the entire word.

**Theorem 1.2 (A descent begins at the global maximum).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.descent_global_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.descent_global_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

In a word avoiding 102 and 210, the first entry of every adjacent descent is at least every entry of the word.

**Theorem 1.3 (Characterization at the first descent).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.first_descent_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.first_descent_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Suppose a word is weakly increasing through position d and then descends at position d + 1. It avoids 010, 100, 102 and 210 if and only if four conditions hold: the entry M at position d is a global maximum; every later entry less than M differs from every prefix entry; the later entries less than M are strictly increasing in their order of occurrence; and whenever a prefix entry lies strictly between the entry at position d + 1 and M, every later entry is less than that prefix entry. The prefix includes position d and the later positions are those greater than d.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.descent_global_maximum`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.first_descent_structure`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.low_value_unique`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs](InversionSeqOccurs.md)
