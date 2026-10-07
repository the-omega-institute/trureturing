# Actual PSL3 UnipotentGeometry

## Abstract

Actual PSL3 UnipotentGeometry.

**Theorem 1.1 (U3 center trivial).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.U3_center_trivial`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.U3_center_trivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, an actual upper-unitriangular determinant-one SL3 matrix in the literal SL3 center equals one: native scalar-center recognition and its unit diagonal force the scalar to one. No central-intersection premise is assumed.

**Theorem 1.2 (quotient U3 injective).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.quotient_U3_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.quotient_U3_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, the actual SL3 central quotient is injective on actual U3. Its kernel is proved trivial using U3_center_trivial; projective upper coordinates remain genuine coordinates.

**Theorem 1.3 (mem projectiveUpperUnipotent).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveUpperUnipotent`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveUpperUnipotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, membership in the actual projective upper subgroup is exactly existence of three field coordinates a,b,c whose literal upper3 matrix has that projective class.

**Theorem 1.4 (projectiveUpperEquiv apply).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine projectiveUpperEquiv from actual U3 to its quotient image applies by the literal central quotient on the actual matrix representative. Its injectivity uses the proved trivial central intersection; it is consumed by the projective center and root proofs.

**Theorem 1.5 (projectiveUpperCoordinate apply).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperCoordinate_apply`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperCoordinate_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projective upper-coordinate equivalence sends v to the class of upper3(v(0),v(1),v(2)). The transported group equivalence preserves the noncommutative three-coordinate structure over every field.

**Theorem 1.6 (projectiveUpperSylow coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperSylow_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperSylow_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of characteristic prime p, the mapped actual SL3 p-Sylow has exactly the literal projective upper subgroup as underlying subgroup. This identity supplies the bare projective automorphism normalization.

**Theorem 1.7 (exists projectiveUpper sylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.exists_projectiveUpper_sylow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.exists_projectiveUpper_sylow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field with a declared prime defining characteristic p, the actual projective upper subgroup is the underlying subgroup of a genuine p-Sylow. Native surjective Sylow mapping is consumed without a simplicity or field-size premise.

**Theorem 1.8 (automorphism projectiveUpper conjugate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field of prime defining characteristic p and every genuine bare PSL3 automorphism beta, beta maps the literal projective upper subgroup to its conjugate by one actual projective element. The proof uses actual Sylow conjugacy and assumes no SL3 automorphism lift.

**Theorem 1.9 (automorphism projectiveUpper normalize).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field of prime defining characteristic p and every bare PSL3 automorphism beta, one actual projective g gives beta(V)=gVg^-1 and (conj g^-1)*beta preserves V. This direction and the actual conjugating element supply the later root and torus normalization.

**Theorem 1.10 (mem projectiveLowerUnipotent iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveLowerUnipotent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveLowerUnipotent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, membership in the literal projective lower subgroup is exactly existence of an SL3 representative with all entries above the diagonal zero and every diagonal entry one. It is the quotient image of the admitted actual lower subgroup.

**Theorem 1.11 (alternating unipotent 25).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.alternating_unipotent_25`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.alternating_unipotent_25` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, every actual PSL3 element has exactly 25 ordered factors, with even indices in the literal projective upper subgroup and odd indices in the literal projective lower subgroup. The actual SL3 decomposition is transported through the genuine quotient, retaining order and actual representatives. This consumed companion supplies the full-group scalar product.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.U3_center_trivial`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.alternating_unipotent_25`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_conjugate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_normalize`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.exists_projectiveUpper_sylow`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveLowerUnipotent_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveUpperUnipotent`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperCoordinate_apply`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperEquiv_apply`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperSylow_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.quotient_U3_injective`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow](PartIISL3UnipotentSylow.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth](PartIISL3UnipotentWidth.md)
