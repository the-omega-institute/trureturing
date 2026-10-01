# A Catalan Bijection for Prefixes

## Abstract

Inversion sequences with increasing positive entries correspond to weakly increasing inversion sequences.

**Definition 1.1 (Retaining increases).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.retainIncreases`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.retainIncreases` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Given a preceding nonnegative value p and a word, retain each entry when it is strictly larger than its immediate predecessor, using p before the first entry, and replace it by zero otherwise. Each comparison uses the predecessor in the original word.

**Theorem 1.2 (A bijection preserving length and maximum).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.catalan_prefix_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.catalan_prefix_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every nonnegative length n and maximum M, inversion sequences of length n and maximum M whose nonzero entries are strictly increasing in order of occurrence are in bijection with weakly increasing inversion sequences of length n and maximum M. The maximum of the empty sequence is taken to be zero.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.catalan_prefix_bijection`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.retainIncreases`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Right](InversionSeq152Right.md)
