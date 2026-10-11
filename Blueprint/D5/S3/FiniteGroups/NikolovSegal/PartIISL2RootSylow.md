# Part II SL2RootSylow

## Abstract

Part II SL2RootSylow.

**Theorem 1.1 (mem upperRoot).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual upper-root subgroup consists exactly of determinant-one transvections upper(t), with t in the field.

**Theorem 1.2 (upper mem upperRoot).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upper_mem_upperRoot`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upper_mem_upperRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual upper transvection belongs to the upper-root subgroup. This supplies the concrete root elements in the subgroup argument.

**Theorem 1.3 (upperHom injective).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperHom_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperHom_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper transvection homomorphism from the multiplicative form of the additive field is injective, by its upper-right matrix entry.

**Theorem 1.4 (mem upperRoot iff fix first).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot_iff_fix_first`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot_iff_fix_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A determinant-one matrix belongs to the actual upper-root subgroup exactly when it fixes the first standard vector. The matrix-entry equations recover the transvection parameter.

**Theorem 1.5 (upperRoot isPGroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_isPGroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_isPGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In characteristic p with p prime, the upper-root subgroup is a p-group because its elements come from the additive field. This includes every finite field of characteristic two or three.

**Theorem 1.6 (pSubgroup fixed vector).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.pSubgroup_fixed_vector`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.pSubgroup_fixed_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of characteristic p, every p-subgroup of SL2 fixes an actual nonzero vector. The fixed-point counting congruence excludes a fixed set containing only zero.

**Theorem 1.7 (upperRoot p maximal).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_p_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_p_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any p-subgroup containing the actual upper-root subgroup equals it. A common nonzero fixed vector is forced onto the first coordinate line, and all subgroup matrices then fix the first standard vector.

**Theorem 1.8 (automorphism upperRoot conjugate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.automorphism_upperRoot_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.automorphism_upperRoot_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every genuine SL2 automorphism over a finite field sends the actual upper-root subgroup to an inner conjugate. The proved p-maximal subgroup is a Sylow subgroup, and Sylow conjugacy supplies the determinant-one matrix; no root-image oracle is a hypothesis.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.automorphism_upperRoot_conjugate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot_iff_fix_first`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.pSubgroup_fixed_vector`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperHom_injective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_isPGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_p_maximal`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upper_mem_upperRoot`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIA1RootSupply](PartIIA1RootSupply.md)
