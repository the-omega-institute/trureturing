# The inner native unit

## Abstract

The inner native unit

**Definition 1.1 (A native series with constant coefficient one).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.innerUnitSeries`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.innerUnitSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In cumulative coefficient coordinates for b,z,x, the exact unit is (1-T-ST)^k (1-T)^k (1+S)^H. It has constant coefficient one over every commutative complex algebra, including the zero algebra.

**Definition 1.2 (Signed native inverse coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.rawInnerCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.rawInnerCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generally infinite native numerator is reordered and placed in the cumulative coefficient chart. The coefficient of the inverse unit times this chart is read at the signed index (b+k,b+z+k+a1+a2,x+b+z+a0+3k+a1+a2), with zero extension outside the nonnegative chart.

**Theorem 1.3 (Exact action of the original polynomial).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite signed monomial translations, sums, products and powers prove that multiplication by the literal original polynomial recovers the original numerator at every signed target. The native unit equation cancels only a native series unit.

**Theorem 1.4 (Support of the inverse expression).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse expression vanishes below b=-k. At each fixed b it vanishes below z=-(b+k+a1+a2), with the signed zero cases included. This proves support of the constructed inverse; it does not impose support on actual fields.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.innerUnitSeries`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.rawInnerCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_action`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.raw_inner_support`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction](ThreeFieldFinalLaurentAction.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial](ThreeFieldInnerPolynomial.md)
