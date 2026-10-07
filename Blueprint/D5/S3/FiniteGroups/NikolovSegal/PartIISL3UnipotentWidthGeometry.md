# Part II SL3UnipotentWidthGeometry

## Abstract

Part II SL3UnipotentWidthGeometry.

**Theorem 1.1 (lower3 mem).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.lower3_mem`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.lower3_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual transpose chart lower3(a,b,c) belongs to the lower-unitriangular SL3 subgroup, over any field.

**Theorem 1.2 (mem lowerUnipotent iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.mem_lowerUnipotent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.mem_lowerUnipotent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the actual lower-unitriangular subgroup is equivalent to all entries above the diagonal being zero and all diagonal entries being one, over every field.

**Theorem 1.3 (block01 coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper-left SL2 embedding is the actual three-by-three matrix with the SL2 block in indices zero and one and a final diagonal entry one.

**Theorem 1.4 (block12 coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower-right SL2 embedding is the actual three-by-three matrix with first diagonal entry one and the SL2 block in indices one and two.

**Theorem 1.5 (block01 upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper-left SL2 embedding sends its upper transvection of parameter t to upper3(t,0,0).

**Theorem 1.6 (block01 lower).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_lower`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper-left SL2 embedding sends its lower transvection of parameter t to lower3(t,0,0).

**Theorem 1.7 (block12 upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower-right SL2 embedding sends its upper transvection of parameter t to upper3(0,t,0).

**Theorem 1.8 (block12 lower).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_lower`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower-right SL2 embedding sends its lower transvection of parameter t to lower3(0,t,0).

**Theorem 1.9 (first pivot).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.first_pivot`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.first_pivot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every SL3 matrix over any field, some upper3(a,0,c) row operation makes the first diagonal entry nonzero. A zero first column would contradict determinant one.

**Theorem 1.10 (eliminate to upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.eliminate_to_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.eliminate_to_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every field, four actual alternating row operations from U3, lower U3, U3, lower U3 make any SL3 matrix upper triangular. The actual nesting v3*(v2*(v1*(v0*g))) and subgroup memberships are retained.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_lower`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_lower`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.eliminate_to_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.first_pivot`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.lower3_mem`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.mem_lowerUnipotent_iff`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure](PartIISL3UnipotentStructure.md)
