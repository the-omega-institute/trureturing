# Enumeration of the Right Avoidance Class

## Abstract

The generating function for 011, 201 and 210 avoiders is expressed in terms of the Catalan series.

**Theorem 1.1 (The right avoidance generating function).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152RightCount.right_avoider_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152RightCount.right_avoider_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Over the rational numbers, let A(x) have constant coefficient one and, in each positive degree n, the number of inversion sequences of length n avoiding 011, 201 and 210. Write C(x) for the Catalan series and t(x) = x C(x). Then 2 (1 - x) (1 - 2 t(x)) (A(x) - 1) = x (2 - 2 t(x)).

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152RightCount.right_avoider_enumeration`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck](InversionSeq152Dyck.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries](InversionSeq152FinalSeries.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix](InversionSeq152Prefix.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Right](InversionSeq152Right.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries](InversionSeq152SuffixSeries.md)
