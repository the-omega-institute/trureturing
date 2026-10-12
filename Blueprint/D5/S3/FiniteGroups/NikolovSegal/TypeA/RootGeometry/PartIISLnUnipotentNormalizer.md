# Type-A SLn Unipotent Normalizer

## Abstract

Type-A SLn Unipotent Normalizer.

The normalizer of the actual full upper unitriangular subgroup of SLn, over every field, in every rank. The canonical coordinate prefixes are derived intrinsically from the subgroup action, using coefficient-one transvections.

**Definition 1.1 (Prefix).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.Prefix`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.Prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vectors supported on the first k coordinates; no bound on k is imposed.

**Theorem 1.2 (prefix succ iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.prefix_succ_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.prefix_succ_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual unitriangular action recovers the next coordinate prefix. The reverse direction uses E_(k,j)(1), so works also in characteristics 2/3.

**Theorem 1.3 (normalizer preserves prefix).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_preserves_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_preserves_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization preserves every coordinate prefix, derived by induction from the actual conjugation law and the intrinsic action characterization.

**Theorem 1.4 (below diagonal zero of normalizer).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.below_diagonal_zero_of_normalizer`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.below_diagonal_zero_of_normalizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalizer element has the actual zero entries below its diagonal.

**Theorem 1.5 (conjugate mem Uplus of upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.conjugate_mem_Uplus_of_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.conjugate_mem_Uplus_of_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Upper triangular conjugation preserves the literal unitriangular carrier.

**Theorem 1.6 (mem normalizer iff upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.mem_normalizer_iff_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.mem_normalizer_iff_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal normalizer/Borel recognition, with no rank or field-size bound.

**Theorem 1.7 (normalizer eq Borel).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_eq_Borel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_eq_Borel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality with the actual determinant-one upper triangular subgroup.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.Prefix`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.below_diagonal_zero_of_normalizer`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.conjugate_mem_Uplus_of_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.mem_normalizer_iff_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_eq_Borel`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_preserves_prefix`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.prefix_succ_iff`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular](../Unitriangular/SLnUnitriangular.md)
