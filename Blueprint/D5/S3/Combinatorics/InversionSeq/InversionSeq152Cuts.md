# Independent Choices of Block Boundaries

## Abstract

Allowed joins between successive labels give independent binary choices for dividing a word into blocks.

**Theorem 1.1 (Enumeration of allowed block divisions).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts.independent_join_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts.independent_join_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Fix a word of nonnegative labels and a nonnegative upper bound u. Divisions into nonempty consecutive blocks whose concatenation is the word and whose tail entries are all less than u are in bijection with the integers from zero through 2 to the power k minus one, where k is the number of entries less than u after the first position. The empty word has one division, consisting of no blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts.independent_join_bijection`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels](InversionSeq152Labels.md)
