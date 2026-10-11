# Type-A Supported Block Extraction

## Abstract

Type-A Supported Block Extraction.

**Definition 1.1 (principalUpper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.principalUpper`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.principalUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extract the genuine ordered principal submatrix; determinant1 follows from the actual ambient unitriangular entries, including d=0.

**Theorem 1.2 (pad double support first).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.pad_double_support_first`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.pad_double_support_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The auxiliary second block really is identity: the embedded double matrix is supported ONLY on the first d selected coordinates.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.pad_double_support_first`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.principalUpper`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues](PartIIFixedCycleBlockValues.md)
