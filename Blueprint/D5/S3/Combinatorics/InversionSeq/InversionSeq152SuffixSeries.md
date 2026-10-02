# Generating Function for Bounded Right Suffixes

## Abstract

Bounded distinct-entry suffixes avoiding 201 and 210 have a generating function determined by binary choices.

**Theorem 1.1 (Enumeration by the first label).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries.first_label_suffix_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries.first_label_suffix_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Fix nonnegative integers l and h. Over the rational numbers, let S(x) have constant coefficient one and, in each positive degree n, the number of words of length n with pairwise distinct entries, all greater than l, avoiding 201 and 210 and satisfying the bound that the entry at position i is at most l + h + 1 + i, with positions numbered from zero. Let B(x) have coefficient 2 to the power n in degree n. Then 2 (1 - x) S(x) = 1 + B(x) to the power h.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries.first_label_suffix_enumeration`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels](InversionSeq152Labels.md)
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity](InversionSeq152Multiplicity.md)
