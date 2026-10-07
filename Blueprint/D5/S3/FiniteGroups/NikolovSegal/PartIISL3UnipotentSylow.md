# Part II SL3UnipotentSylow

## Abstract

Part II SL3UnipotentSylow.

**Theorem 1.1 (U3 isPGroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_isPGroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_isPGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of characteristic p, the actual upper-unitriangular subgroup is a p-group. Its three-coordinate cardinality is a power of p; the statement does not require a separate primality hypothesis.

**Theorem 1.2 (pSubgroup fixed vector).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.pSubgroup_fixed_vector`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.pSubgroup_fixed_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of prime characteristic p, every p-subgroup of SL3 fixes an actual nonzero vector in F^3, by the fixed-point counting congruence.

**Theorem 1.3 (p overgroup fix first).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.p_overgroup_fix_first`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.p_overgroup_fix_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of prime characteristic p, any p-subgroup containing actual U3 fixes the first standard vector pointwise. The bottom-right SL2 action reduces the last two coordinates to upper-root maximality.

**Theorem 1.4 (U3 p maximal).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_p_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_p_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of prime characteristic p, any p-subgroup containing actual U3 equals U3. No field-size lower bound is required.

**Theorem 1.5 (exists U3 sylow).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.exists_U3_sylow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.exists_U3_sylow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of prime characteristic p, there is a Sylow p-subgroup of SL3 whose underlying subgroup is the actual U3.

**Theorem 1.6 (automorphism U3 conjugate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.automorphism_U3_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.automorphism_U3_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every finite field of prime characteristic p, every bare SL3 automorphism maps actual U3 to its conjugate by an actual determinant-one matrix. Sylow maximality and conjugacy include the fields of sizes two and three.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_isPGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.U3_p_maximal`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.automorphism_U3_conjugate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.exists_U3_sylow`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.pSubgroup_fixed_vector`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow.p_overgroup_fix_first`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure](PartIISL3UnipotentStructure.md)
