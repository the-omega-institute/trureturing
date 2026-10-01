# Factorizations at the Initial Ascent and Final Descent

## Abstract

Lists of Dyck paths factor a Dyck path at its initial ascent or final descent.

**Definition 1.1 (Assembly at the initial ascent).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentWord`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Starting with the empty Dyck path, read a list of factors from left to right. At each factor, surround the current path with an up step and a down step, then concatenate the factor. This defines the path assembled at its initial ascent.

**Definition 1.2 (Assembly at the final descent).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.descentWord`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.descentWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Starting with the empty Dyck path, read a list of factors from right to left. At each factor, concatenate that factor with the current path surrounded by an up step and a down step. This defines the path assembled at its final descent.

**Definition 1.3 (Factors along the initial ascent).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentFactors`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentFactors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The empty Dyck path has no ascent factors. For a nonempty Dyck path, factor the portion enclosed by its first matching up and down steps recursively, then append the remaining exterior portion as the last factor.

**Theorem 1.4 (Two bijective run factorizations).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.runFactorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.runFactorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Both assemblies are bijections from lists of Dyck paths to Dyck paths. With k factors, the ascent assembly consists of k up steps followed by each factor preceded by a down step, and its initial ascent has length k. The descent assembly consists of each factor followed by an up step, then k down steps, and its final descent has length k. In both cases the semilength is k plus the sum of factor semilengths. The ascent lengths of the ascent assembly are its initial ascent, when nonempty, followed by all ascent lengths of the factors. The inverse of ascent assembly is recursive ascent factorization; the inverse of descent assembly reflects the path, takes its ascent factors, reverses their order and reflects each factor.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentFactors`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.ascentWord`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.descentWord`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.runFactorization`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalReverse](../Nonnesting/NonnestingBasicRoyalReverse.md)
