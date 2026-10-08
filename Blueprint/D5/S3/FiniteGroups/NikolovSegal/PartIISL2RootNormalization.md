# Part II SL2RootNormalization

## Abstract

Part II SL2RootNormalization.

**Theorem 1.1 (root inverse addEquiv ring).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.root_inverse_addEquiv_ring`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.root_inverse_addEquiv_ring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every finite field, an additive equivalence fixing one and preserving inversion is a ring automorphism. Hua identities yield multiplication in characteristic different from two; the finite-field square map resolves characteristic two. No lower bound on field size is imposed here.

**Theorem 1.2 (a1Weyl product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field and nonzero x, the ordered upper(x), lower(-inverse(x)), upper(x) product equals the explicit determinant-one Weyl matrix.

**Theorem 1.3 (a1Weyl upper).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_upper`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by the explicit Weyl matrix takes upper(t) to lower(-(inverse(x))^2 t) for nonzero x over any field.

**Theorem 1.4 (actual root pair SL2 scalar product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_pair_SL2_scalar_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_pair_SL2_scalar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Additive coordinate equivalences for the two actual SL2 roots determine field actions by Weyl and Hua relations in both characteristics. This constructs the scalar PRODUCT from the stated genuine root laws, under the field and length bounds, without a semilinearity premise.

**Theorem 1.5 (actual root coordinate equiv).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_coordinate_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_coordinate_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an injective additive root parametrization in any group, an automorphism preserving its actual range induces an additive equivalence on the field coordinates. Range equality provides the inverse map; the root multiplication law gives additivity.

**Theorem 1.6 (actual root stabilizing SL2 scalar product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_stabilizing_SL2_scalar_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_stabilizing_SL2_scalar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Automorphisms preserving the actual upper and lower SL2 root ranges satisfy the scalar PRODUCT under the quantitative bounds. Additive root coordinates and their field action are constructed, rather than supplied as assumptions.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.a1Weyl_upper`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_coordinate_equiv`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_pair_SL2_scalar_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.actual_root_stabilizing_SL2_scalar_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization.root_inverse_addEquiv_ring`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL2Projective](PartIISL2Projective.md)
