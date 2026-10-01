# Structure of the Right Avoidance Class

## Abstract

Avoidance of 011, 201 and 210 separates at the last zero of an inversion sequence.

**Theorem 1.1 (Distinct positive entries).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.avoid011_iff_positive_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.avoid011_iff_positive_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

An inversion sequence avoids 011 if and only if its positive entries are pairwise distinct.

**Theorem 1.2 (Characterization at the last zero).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.right_last_zero_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.right_last_zero_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Suppose an inversion sequence has its last zero at position z. It avoids 011, 201 and 210 if and only if its positive entries are pairwise distinct, its positive entries through position z are strictly increasing in order of occurrence, every entry through position z is less than every later entry, and no three increasing positions after z have their first entry larger than both their second and third entries.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.avoid011_iff_positive_distinct`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.right_last_zero_structure`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs](InversionSeqOccurs.md)
