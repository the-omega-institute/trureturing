# Ordered coefficients of analytic factors

## Abstract

Spatial Taylor extraction through the Wick recursion

**Definition 1.1 (Dependence on selected coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.DependsOn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.DependsOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function takes equal values at any two inputs that agree on the selected coordinates.

**Theorem 1.2 (Extraction on disjoint coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_filter`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For factors supported on the true and false fibres of a Boolean predicate, the ordered Taylor coefficients on the corresponding filtered subwords multiply to the coefficient of the product at any evaluation point.

**Theorem 1.3 (Recovering the two ordered subwords).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.partition_eq_filters`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.partition_eq_filters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word of distinct labels and a position partition, filtering by membership in the first subword gives that subword. Filtering by its complement gives the second subword.

**Theorem 1.4 (Extraction on a position partition).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When each factor depends only on its own subword of a distinct occurrence word, the ordered Taylor coefficient of the product factors along the partition at any evaluation point.

**Theorem 1.5 (Occurrence support of Wick evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_dependsOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_dependsOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spatial Wick evaluation depends on the coordinates in the occurrence word, because each singleton and pair in the recursion uses only those coordinates.

**Theorem 1.6 (Additivity on analytic germs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two germs analytic at zero, applying the ordered spatial coefficient at zero to their sum gives the sum of their coefficients.

**Theorem 1.7 (Analyticity of Wick evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finitely many coordinates, analyticity at zero of the pair and singleton entries implies analyticity of the Wick evaluation for any occurrence word.

**Theorem 1.8 (Extraction through a finite list sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_list_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_list_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at zero of a list sum of analytic germs equals the sum of their coefficients, counted with the multiplicities of the list.

**Theorem 1.9 (Extraction into the Wick entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_wick`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_wick` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a distinct occurrence word and pair and singleton germs analytic at zero, the spatial coefficient of the Wick evaluation equals its Wick value with extracted entries. Take the singleton coefficient at its mode and each pair coefficient at both modes in occurrence order.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.DependsOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.partition_eq_filters`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_add`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_list_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_filter`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_partition`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.spatialCoefficient_wick`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.wick_dependsOn`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor](OriginalFourMSpatialTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution](../Wick/AffineWickConvolution.md)
