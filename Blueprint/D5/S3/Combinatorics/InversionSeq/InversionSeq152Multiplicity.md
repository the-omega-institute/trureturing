# Multiplicities of Ordered Binary Choices

## Abstract

Sorted labelled binary choices separate into label multiplicities and one binary word for each label.

**Theorem 1.1 (Multiplicity decomposition and enumeration).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity.ordered_choice_multiplicity_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity.ordered_choice_multiplicity_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let A be a finite linearly ordered set with a specified set of permitted labels, and fix a nonnegative length n. Words of n label-bit pairs with weakly increasing labels and false bits at all nonpermitted labels are in bijection with multiplicities on A summing to n together with, for each label, a binary word of its multiplicity, constrained to be all false for nonpermitted labels. Each binary word is exactly the subsequence of bits at its label in the original word. For fixed multiplicities, the number of such families is the product over labels of 2 to the power of the multiplicity for permitted labels and 1 to that power for other labels.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity.ordered_choice_multiplicity_bijection`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts](InversionSeq152Cuts.md)
