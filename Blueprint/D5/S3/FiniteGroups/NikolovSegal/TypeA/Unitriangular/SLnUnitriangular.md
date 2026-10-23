# Type-A SLn Unitriangular

## Abstract

Type-A SLn Unitriangular.

Actual upper unitriangular and upper triangular subgroups of SLn. block-triangular multiplication and inversion are reused.

**Definition 1.1 (Upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Upper`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal zero entries strictly below the diagonal.

**Theorem 1.2 (upper mul diag).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.upper_mul_diag`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.upper_mul_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonal multiplication uses only the literal triangular entries.

**Definition 1.3 (Uplus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Uplus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Uplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual full upper-unitriangular subgroup, in every rank and field.

**Definition 1.4 (Borel).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Borel`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Borel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual determinant-one upper triangular subgroup.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Borel`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Uplus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.Upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular.upper_mul_diag`
