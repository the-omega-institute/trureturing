# Type-A Unitriangular Layers

## Abstract

Type-A Unitriangular Layers.

Nikolov--Segal Part II p264 equation(13): the actual leading matrix commutator map of a proper unitriangular matrix. This is the rank-independent linear kernel needed by Proposition6.5, not full U coverage.

**Definition 1.1 (layerStrip).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.layerStrip`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.layerStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal kth superdiagonal matrix, with every other entry zero.

**Theorem 1.2 (actual layer bracket coordinate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_layer_bracket_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_layer_bracket_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual matrix Lie commutator, preserving the genuine two unequal coefficients and their order. No constant-coefficient or graph hypothesis.

**Theorem 1.3 (actual proper layer bracket surjective).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_layer_bracket_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_layer_bracket_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prescribed next-layer coordinate is realized by the ACTUAL matrix commutator with a proper matrix. The recursively solved strip is one layer wide; the bound/length does not depend on n. This proves the surjectivity of the printed linear kernel before its group-filtration use.

**Definition 1.4 (LayerDepth).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.LayerDepth`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.LayerDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal matrix height filtration used in printed equation(13).

**Definition 1.5 (stripUnit).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.stripUnit`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.stripUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual determinant-one strip witness in the genuine kth layer.

**Theorem 1.6 (actual proper group layer surjective).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_group_layer_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_group_layer_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Printed equation(13)'s ACTUAL group-commutator leading-layer surjectivity in arbitrary matrix rank. The witness lies in the true kth layer and is constructed, not assumed; the proper matrix is genuine SL. This does not yet assert Proposition6.5 or a full unbounded-rank supplier.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.LayerDepth`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_layer_bracket_coordinate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_group_layer_surjective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.actual_proper_layer_bracket_surjective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.layerStrip`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers.stripUnit`
