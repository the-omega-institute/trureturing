# Part II SL3UnipotentWidth

## Abstract

Part II SL3UnipotentWidth.

**Theorem 1.1 (triangular factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.triangular_factor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.triangular_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every upper-triangular determinant-one three-by-three matrix factors as the upper-left diag2(a) block, the lower-right diag2(b) block, and one actual U3 element, with a and b nonzero.

**Theorem 1.2 (diagonal01 factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal01_factor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal01_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero a over any field, the actual upper-left diag2(a) block is the ordered six-factor product upper3(a,0,0), lower3(-a inverse,0,0), upper3(a,0,0), upper3(-1,0,0), lower3(1,0,0), upper3(-1,0,0).

**Theorem 1.3 (diagonal12 factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal12_factor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal12_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero b over any field, the actual lower-right diag2(b) block is the ordered six-factor product upper3(0,b,0), lower3(0,-b inverse,0), upper3(0,b,0), upper3(0,-1,0), lower3(0,1,0), upper3(0,-1,0).

**Theorem 1.4 (alternating unipotent 25).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.alternating_unipotent_25`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.alternating_unipotent_25` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual SL3 matrix over every field is an ordered product of exactly 25 factors, in actual upper U3 at even indices and lower U3 at odd indices. Four pivot operations, two embedded SL2 diagonal decompositions and identity padding supply the witnesses, including fields of sizes two and three.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.alternating_unipotent_25`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal01_factor`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal12_factor`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.triangular_factor`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry](PartIISL3UnipotentWidthGeometry.md)
