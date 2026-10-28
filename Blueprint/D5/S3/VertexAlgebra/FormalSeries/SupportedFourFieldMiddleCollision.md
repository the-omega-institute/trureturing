# Native middle collision

## Abstract

Native middle collision

**Theorem 1.1 (Original first and fourth spectators).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleSlice_extend`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleSlice_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any commutative complex algebra and any generally infinite four-variable power series P, the bivariate slice fixes original labels zero and three at arbitrary signed x,y. Its signed extension at v,t is exactly signedExtend P at x,v,t,y, including either negative spectator or active coordinate.

**Theorem 1.2 (Native substitution at x,b+z,z,y).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleCollision_signed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleCollision_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed x,b,z,y, the signed coefficient of the legal native substitution P[X0,X1+X2,X2,X3] equals the bivariate collision of the original u,q slice at b,z. The change of labels is the permutation zero,two,three,one and its inverse. The existing four-field native collision supplies the coefficient law after this permutation. Only power series with nonnegative native indices are substituted; arbitrary raw distributions are never substituted. Carnahan attribution for the supported collision supplier is preserved.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleCollision_signed`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.middleSlice_extend`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision](SupportedFourFieldCollision.md)
