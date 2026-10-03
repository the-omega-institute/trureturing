# Enumeration of Gap Suffixes

## Abstract

Strictly increasing gap words and words interspersed with a maximum have binomial enumerations.

**Theorem 1.1 (Subset and multiset enumerations).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount.gap_suffix_enumerators`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount.gap_suffix_enumerators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let G be a finite set of nonnegative integers all less than M, and let l be nonnegative. Strictly increasing words of length l + 1 over G are in bijection with subsets of G of size l + 1, and their number is the binomial coefficient choosing l + 1 from the cardinality of G. Words of length l + 1 over G together with M, whose first entry is not M and whose entries remaining after deleting M are strictly increasing, are in bijection with multisets over G of size l + 1. Their number is the binomial coefficient choosing l + 1 from the cardinality of G plus l.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount.gap_suffix_enumerators`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Left](InversionSeq152Left.md)
