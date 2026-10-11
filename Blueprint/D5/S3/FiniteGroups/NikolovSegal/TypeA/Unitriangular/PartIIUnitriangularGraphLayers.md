# Type-A Unitriangular Graph Layers

## Abstract

Type-A Unitriangular Graph Layers.

**Definition 1.1 (mirrorWeight).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorWeight`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Printed p265 symmetric alternating torus, as integral diagonal weights. For odd matrix size, opposite sides of the central unit have inverse weights; for even size the alternating zero and minus-one pattern works modulo scalars.

**Theorem 1.2 (actual mirror odd root weights).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_odd_root_weights`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_odd_root_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two quantitative torus facts are derived for ACTUAL matrix indices, including central-crossing roots. No sign/commutation law input.

**Definition 1.3 (mirrorTorus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorTorus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine p265 reflection-invariant torus on arbitrary-rank SL.

**Theorem 1.4 (actual mirror field graph doubled power).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_field_graph_doubled_power`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_field_graph_doubled_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual doubled-power odd-root transport for arbitrary prescribed field/positive-graph actions. Reflection-invariant torus weights and the component formula are proved, not assumed. This is the p265--266 scalar bridge; it does not assume scalar or matrix product coverage.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_field_graph_doubled_power`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.actual_mirror_odd_root_weights`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorTorus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers.mirrorWeight`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayersGlobal](PartIIUnitriangularLayersGlobal.md)
