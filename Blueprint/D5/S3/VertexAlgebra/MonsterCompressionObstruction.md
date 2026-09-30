# Ground-Section Compression Obstructs Spin Descent

## Abstract

An additive compression of all ground sections erases every character direction and cannot preserve quadratic spin.

Let E be the three-dimensional binary vector space and let a finite sign table satisfy the character-carry equations. Each ground section has a defect coordinate and a character coordinate.

**Theorem 1.1 (Character kernel and failure of spin descent).**

Lean statement: `D5/S3/VertexAlgebra/MonsterCompressionObstruction.compression_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterCompressionObstruction.compression_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

For every target abelian group and additive map from the six-bit label group, requiring the images of all ground sections to add as coarse defects forces every pure character label into the kernel. Two labels then have the same image but different quadratic spin values, so the spin cannot factor through the map. The proof uses three independent determinant-carry directions and works for every permitted sign table. Basak's twisted-group-algebra calculation is historical background. This finite-label result assumes no VOA realization, physical fusion operation, or condensation procedure.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterCompressionObstruction.compression_obstruction`
- Dependency: [D5/S3/VertexAlgebra/MonsterFusionSpan](MonsterFusionSpan.md)
