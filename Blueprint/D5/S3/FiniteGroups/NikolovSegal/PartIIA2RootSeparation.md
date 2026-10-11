# Part II A2RootSeparation

## Abstract

Part II A2RootSeparation.

**Theorem 1.1 (fixed first torus kernel iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_first_torus_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_first_torus_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of size greater than four and g in actual U3, commuting with every diagonalPair(x,x) is equivalent to membership in the first simple-root subgroup.

**Theorem 1.2 (fixed second torus kernel iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_second_torus_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_second_torus_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of size greater than four and g in actual U3, commuting with every diagonalPair((x*x) inverse,x) is equivalent to membership in the second simple-root subgroup.

**Theorem 1.3 (actual torus kernel classification).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_torus_kernel_classification`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_torus_kernel_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a subgroup of the actual diagonal torus with cardinality equal to that of F units. If L centralizes upper3(a,b,c), where a or b is nonzero, then L is exactly firstKernel or secondKernel. The statement retains the exact cardinal equality and requires no field-size lower bound.

**Theorem 1.4 (actual normalized simple root permutation).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_normalized_simple_root_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_normalized_simple_root_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of size greater than four, an automorphism preserving actual U3, the torus and the central root either preserves both simple-root subgroups or exchanges them. The possibilities follow from actual torus kernels and root incidence.

**Theorem 1.5 (actual bare SL3 root normalization).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_bare_SL3_root_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_bare_SL3_root_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite field of size greater than four, every bare SL3 automorphism has an actual inner correction preserving U3 and the central root and either preserving both simple roots or exchanging them. These subgroup laws are conclusions, not additional premises.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_bare_SL3_root_normalization`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_normalized_simple_root_permutation`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.actual_torus_kernel_classification`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_first_torus_kernel_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation.fixed_second_torus_kernel_iff`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry](PartIIA2RootGeometry.md)
