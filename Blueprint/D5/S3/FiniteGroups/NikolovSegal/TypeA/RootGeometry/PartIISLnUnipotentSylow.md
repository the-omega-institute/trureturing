# Type-A SLn Unipotent Sylow

## Abstract

Type-A SLn Unipotent Sylow.

The actual SLn upper-unitriangular subgroup is Sylow in every finite field of defining characteristic. GL cardinality and Sylow pullback avoid a redundant SL group-order computation.

**Theorem 1.1 (card GL factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.card_GL_factor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.card_GL_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine GL order split into its upper-entry power and remaining factors.

**Definition 1.2 (GLupper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual image of the literal Uplus in GL.

**Theorem 1.3 (GLupper index).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual GL index of Uplus, derived from GL order and proved entry bijection.

**Theorem 1.4 (Uplus isPGroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.Uplus_isPGroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.Uplus_isPGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Defining-characteristic p-group recognition from the actual cardinality.

**Theorem 1.5 (GLupper index not dvd).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index_not_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index_not_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every remaining GL index factor is prime to the actual field characteristic.

**Definition 1.6 (UplusSylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A genuine Sylow with exactly the literal SLn unitriangular carrier. It is the injective pullback of the actual GL-image Sylow.

**Theorem 1.7 (UplusSylow toSubgroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow_toSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow_toSubgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal underlying-subgroup equality, not an assumed Sylow recognition premise.

**Theorem 1.8 (exists Uplus sylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.exists_Uplus_sylow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.exists_Uplus_sylow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime, every finite field of characteristic p and every rank, including0/1.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.GLupper_index_not_dvd`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.UplusSylow_toSubgroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.Uplus_isPGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.card_GL_factor`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow.exists_Uplus_sylow`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard](../Unitriangular/SLnUnitriangularCard.md)
