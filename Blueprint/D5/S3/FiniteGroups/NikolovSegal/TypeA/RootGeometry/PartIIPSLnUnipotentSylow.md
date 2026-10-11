# Type-A PSLn Unipotent Sylow

## Abstract

Type-A PSLn Unipotent Sylow.

Actual arbitrary-rank projective Uplus Sylow recognition. The SLn Sylow is transported through the actual surjective center quotient by Sylow.mapSurjective; no projective group order is recomputed.

**Definition 1.1 (projectiveUplusSylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

surjective Sylow transport through the literal SLn center quotient.

**Theorem 1.2 (projectiveUplusSylow toSubgroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow_toSubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow_toSubgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual underlying subgroup is exactly the projective Uplus.

**Theorem 1.3 (exists projectiveUplus sylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.exists_projectiveUplus_sylow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.exists_projectiveUplus_sylow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime, finite field of characteristic p, and rank, without a cutoff.

**Theorem 1.4 (mem projectiveUplusSylow iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.mem_projectiveUplusSylow_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.mem_projectiveUplusSylow_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal membership recognition by actual unitriangular determinant-one representatives, retaining the genuine quotient and both entry conditions.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.exists_projectiveUplus_sylow`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.mem_projectiveUplusSylow_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow_toSubgroup`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer](PartIIPSLnUnipotentNormalizer.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow](PartIISLnUnipotentSylow.md)
