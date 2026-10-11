# Type-A Unitriangular Field Supply

## Abstract

Type-A Unitriangular Field Supply.

**Definition 1.1 (layerTorus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.layerTorus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.layerTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual diagonal torus for the fixed kth layer: every kth-height root has weight lambda. Its first/second-layer instances are the two printed last batches of Proposition6.5, with no rank-dependent field exponent.

**Theorem 1.2 (actual uniform field fixed layer product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_fixed_layer_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_fixed_layer_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual fixed-layer scalar product, consumed for the two leading layers of Proposition6.5. Exact diagonal/field powers, genuine strip witnesses and all matrix target coordinates are reconstructed from proved Lemma7.1. Corrections precede every target and M/cutoff are independent of rank.

**Theorem 1.3 (actual uniform field U product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_U_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_U_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete FIELD-action branch of printed PartII Proposition6.5, all finite matrix ranks. Four ordered batches and the one actual powered proper correction cover the ENTIRE upper unitriangular group. Scalar choices, diagonal corrections and u0 precede all targets; M and field cutoff are independent of rank. The first/second layers are genuinely solved and the residual is consumed by the full U3 reconstruction. This is not graph-tuple/bare-auto/all-simple scalar supply.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_U_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.actual_uniform_field_fixed_layer_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply.layerTorus`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayersGlobal](PartIIUnitriangularLayersGlobal.md)
