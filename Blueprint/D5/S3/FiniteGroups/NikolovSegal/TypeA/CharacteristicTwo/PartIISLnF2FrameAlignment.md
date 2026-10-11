# Type-A SLn F2 Frame Alignment

## Abstract

Type-A SLn F2 Frame Alignment.

**Theorem 1.1 (frameMatrix upper diag).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameMatrix_upper_diag`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameMatrix_upper_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit completion of the last column; all earlier columns are the rank-one image vectors. Its diagonal and triangularity are genuine.

**Theorem 1.2 (frameLast pairing).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameLast_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameLast_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last-column correction solves the whole triangular covector system, not a target-dependent or assumed basis choice.

**Theorem 1.3 (frameSL conjugates).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameSL_conjugates`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameSL_conjugates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One explicit actual determinant-one U matrix simultaneously conjugates all simple roots to the given rank-one frame.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameLast_pairing`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameMatrix_upper_diag`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FrameAlignment.frameSL_conjugates`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2RankOneFrame](PartIISLnF2RankOneFrame.md)
