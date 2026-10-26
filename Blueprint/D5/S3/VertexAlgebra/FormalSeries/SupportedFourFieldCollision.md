# Admissible native arguments

## Abstract

Admissible native arguments

**Theorem 1.1 (Admissible native arguments).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInner_hasSubst`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInner_hasSubst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four native power series arguments are X0, X1, X2+X3 and X3. Each has zero constant coefficient, so substitution is defined for a generally infinite input series.

**Theorem 1.2 (Finite collision coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a generally infinite four-variable series P over a commutative complex algebra, the coefficient at x,y,a,b after native collision equals the sum over 0 through b of choose(a+j,a) times the original coefficient at x,y,a+j,b-j. Both spectator labels remain fixed. The finite fiber follows from the substituted monomial coefficients, without any finite-support assumption on P.

**Theorem 1.3 (Two signed spectator slices).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.slice_extend`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.slice_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixing two signed spectator indices defines a native bivariate slice of the same original P. Its zero extension equals the four-variable signed extension on those fixed indices, including negative collision and spectator regions.

**Theorem 1.4 (Signed native collision).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_signed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed extension of the native four-variable collision equals the existing bivariate collision on the fixed two-spectator slice. Every signed coordinate is allowed. If either spectator index is negative the slice and both readouts vanish. Carnahan binomial collision identities are retained through the bivariate supplier.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInnerCollision_signed`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.fourInner_hasSubst`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.slice_extend`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision](SupportedThreeFieldCollision.md)
