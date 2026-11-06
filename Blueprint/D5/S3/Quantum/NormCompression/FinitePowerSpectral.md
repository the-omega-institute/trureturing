# Two eigenvalue chart and boundary regularization

## Abstract

Exact spectral chart and full boundary regularization for finite two row trace powers.

**Definition 1.1 (Regularizing boundary columns).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundaryTable`

*Formalization.* `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundaryTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The appended table has columns epsilon (1,1) and epsilon (1,4). Its Aq columns are epsilon^(1/(2q)) (1,1) and epsilon^(1/(2q)) (1,4^(1/(2q))).

**Definition 1.2 (Positive regularization of the original table).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable`

*Formalization.* `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original columns receive epsilon in each entry, followed by the two explicit independent boundary columns. This construction retains the original finite column type and adds only two columns.

**Theorem 1.3 (Independent boundary columns).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundary_gram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundary_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive q and epsilon the actual boundary row Gram is positive definite.

**Theorem 1.4 (Strictly positive regularization).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry is positive for positive epsilon and a nonnegative original table.

**Theorem 1.5 (Positive definite row Gram).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularized_gram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularized_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual regularized row Gram is positive definite, even when the original column type is empty.

**Theorem 1.6 (Full boundary recovery).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.tendsto_regularized_Fq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerSpectral.tendsto_regularized_Fq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual regularized Schatten trace power tends to the original Fq as epsilon tends to zero.

**Theorem 1.7 (Exact two dimensional spectral chart).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.Fq_eq_two_eigenvalue_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerSpectral.Fq_eq_two_eigenvalue_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q positive and an entrywise nonnegative table, the explicit two eigenvalue formula equals the actual Schatten trace power. It includes singular and repeated eigenvalues.

All formulas identify the actual operator trace; no curvature premise is assumed.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.Fq_eq_two_eigenvalue_formula`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundaryTable`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundary_gram_posDef`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable_pos`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularized_gram_posDef`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerSpectral.tendsto_regularized_Fq`
- Dependency: [D5/S3/Quantum/NormCompression/FinitePowerTrace](FinitePowerTrace.md)
