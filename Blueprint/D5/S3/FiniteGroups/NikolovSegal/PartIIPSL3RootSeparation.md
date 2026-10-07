# Actual PSL3 RootSeparation

## Abstract

Actual PSL3 RootSeparation.

**Theorem 1.1 (actual normalized projective simple root permutation).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_normalized_projective_simple_root_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_normalized_projective_simple_root_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of size greater than four, a genuine projective automorphism preserving actual U3, diagonal torus and central root preserves the two actual simple root subgroups as a pair. Quotient torus preimages and actual kernel fixed-point arithmetic prove the alternatives, without assuming their images.

**Theorem 1.2 (actual bare PSL3 root normalization).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_bare_PSL3_root_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_bare_PSL3_root_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of size greater than four, every bare PSL3 automorphism admits one actual projective correction preserving U3 and the central root, with the two simple roots either retained or swapped. The real subgroup geometry supplies the root alternatives; no root-image or lift oracle is used.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_bare_PSL3_root_normalization`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation.actual_normalized_projective_simple_root_permutation`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootSeparation](PartIIA2RootSeparation.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3TorusAlignment](PartIIPSL3TorusAlignment.md)
