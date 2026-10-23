# Type-A PSLn Torus Alignment

## Abstract

Type-A PSLn Torus Alignment.

Actual all-rank projective torus alignment. The whole central-quotient preimage is averaged, following the PartIIPSL3TorusAlignment proof. No projective automorphism lift is assumed or constructed.

**Definition 1.1 (projectiveDiagonalTorus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.projectiveDiagonalTorus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.projectiveDiagonalTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual quotient image of the literal determinant-one diagonal torus.

**Theorem 1.2 (card torus image preimage).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.card_torus_image_preimage`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.card_torus_image_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual index arithmetic proves the full torus-image preimage has the original SL torus order. It retains every scalar in the actual center.

**Theorem 1.3 (U preserving torus alignment).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.U_preserving_torus_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.U_preserving_torus_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A further actual projective inner correction preserves U and aligns T by averaging its whole SL preimage, without lifting the automorphism.

**Theorem 1.4 (psl inner U T correction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.psl_inner_U_T_correction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.psl_inner_U_T_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One genuine projective inner correction, before all targets, preserves actual full projective U and T in every rank and characteristic.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.U_preserving_torus_alignment`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.card_torus_image_preimage`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.projectiveDiagonalTorus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment.psl_inner_U_T_correction`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment](PartIISLnTorusAlignment.md)
