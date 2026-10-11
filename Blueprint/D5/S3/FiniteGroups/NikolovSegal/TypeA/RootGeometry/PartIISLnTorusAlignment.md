# Type-A SLn Torus Alignment

## Abstract

Type-A SLn Torus Alignment.

Actual all-rank diagonal-torus alignment. The weighted matrix average generalizes the PartIIA2TorusAlignment (rank3) proof, without a complement-conjugacy or classification assumption.

**Theorem 1.1 (upper finite subgroup diagonal alignment).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.upper_finite_subgroup_diagonal_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.upper_finite_subgroup_diagonal_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One actual Uplus element simultaneously aligns a whole finite triangular subgroup whenever its genuine order is invertible in the field.

**Definition 1.2 (torusDiagonalUnits).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.torusDiagonalUnits`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.torusDiagonalUnits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Genuine diagonal-entry embedding of the literal SL torus into units.

**Theorem 1.3 (card torus dvd units).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.card_torus_dvd_units`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.card_torus_dvd_units` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No order oracle: Lagrange applied to the actual unit-entry embedding.

**Theorem 1.4 (U preserving torus alignment).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.U_preserving_torus_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.U_preserving_torus_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Further correction of an actual U-preserving automorphism by an actual Uplus element. Its torus-image order and triangularity are derived.

**Theorem 1.5 (sl inner U T correction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.sl_inner_U_T_correction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.sl_inner_U_T_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One actual determinant-one inner correction, before all targets, preserves full Uplus and the literal diagonal torus in every rank.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.U_preserving_torus_alignment`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.card_torus_dvd_units`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.sl_inner_U_T_correction`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.torusDiagonalUnits`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment.upper_finite_subgroup_diagonal_alignment`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnInnerUNormalization](PartIISLnInnerUNormalization.md)
