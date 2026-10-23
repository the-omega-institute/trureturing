# Type-A PSLn Unipotent Normalizer

## Abstract

Type-A PSLn Unipotent Normalizer.

The actual projective upper-unitriangular normalizer in every rank, over every field. The actual SLn normalizer proof is imported unchanged. Characteristic polynomials eliminate central discrepancies without any rank, characteristic, finiteness or automorphism-lift premise.

**Definition 1.1 (projectiveUplus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projectiveUplus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projectiveUplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual central-quotient image of the full SLn upper unitriangular subgroup.

**Theorem 1.2 (scalar unitriangular charpoly).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.scalar_unitriangular_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.scalar_unitriangular_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

triangular characteristic-polynomial recognition applied to the actual scalar multiple of a literal unitriangular matrix.

**Theorem 1.3 (conjugate eq of quotient eq).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.conjugate_eq_of_quotient_eq`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.conjugate_eq_of_quotient_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of projective conjugates of actual unitriangular matrices lifts to actual SLn equality. The rank0/1 cases use subsingletons; in positive higher ranks evaluation of the actual charpoly at1 forces the central scalar z to equal1, even when the characteristic divides the rank.

**Theorem 1.4 (projective conjugate mem iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_conjugate_mem_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_conjugate_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projective conjugation membership lifts on the actual unitriangular carrier.

**Theorem 1.5 (quotient mem normalizer iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact normalizer preimage under the actual central quotient.

**Theorem 1.6 (quotient mem normalizer iff upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal every-field/all-rank recognition of projective normalization.

**Theorem 1.7 (mem projective normalizer iff upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.mem_projective_normalizer_iff_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.mem_projective_normalizer_iff_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual projective element normalizes precisely when it admits an actual determinant-one upper triangular representative.

**Theorem 1.8 (projective normalizer eq map Borel).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_normalizer_eq_map_Borel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_normalizer_eq_map_Borel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of actual subgroups: the projective normalizer is the quotient image of the literal determinant-one Borel, in every rank and field.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.conjugate_eq_of_quotient_eq`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.mem_projective_normalizer_iff_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projectiveUplus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_conjugate_mem_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_normalizer_eq_map_Borel`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.scalar_unitriangular_charpoly`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer](PartIISLnUnipotentNormalizer.md)
