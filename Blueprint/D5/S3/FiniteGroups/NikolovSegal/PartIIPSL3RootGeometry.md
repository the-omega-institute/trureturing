# Actual PSL3 RootGeometry

## Abstract

Actual PSL3 RootGeometry.

**Theorem 1.1 (mem center projective U3 iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.mem_center_projective_U3_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.mem_center_projective_U3_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, the center of actual projective U3 consists exactly of classes of upper3(0,0,t). The genuine quotient/U3 equivalence transports the computed matrix center, with no central-root image hypothesis.

**Theorem 1.2 (actual projective U preserving central root map).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_projective_U_preserving_central_root_map`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_projective_U_preserving_central_root_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field, every genuine PSL3 automorphism preserving actual projective U3 preserves its literal central positive root. Center transport uses the actual restricted automorphism, and finite-cardinality comparison proves equality of the subgroups.

**Theorem 1.3 (actual bare PSL3 U central root normalization).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_bare_PSL3_U_central_root_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_bare_PSL3_U_central_root_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every finite field, every bare PSL3 automorphism has one actual projective inner normalization preserving U3 and its computed central root. Its defining characteristic and actual Sylow conjugacy are derived; no automorphism lift, cutoff or root-image premise is assumed.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_bare_PSL3_U_central_root_normalization`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.actual_projective_U_preserving_central_root_map`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry.mem_center_projective_U3_iff`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry](PartIIA2RootGeometry.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry](PartIIPSL3UnipotentGeometry.md)
