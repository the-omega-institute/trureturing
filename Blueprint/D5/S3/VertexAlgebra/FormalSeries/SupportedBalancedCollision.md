# Balanced native collision

## Abstract

Balanced native collision

**Definition 1.1 (The original cross factors).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCross`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite action of (y-z)^k(x-z)^k on the original labelled coefficients. The u/v factor is applied separately to recover the exact original clearing polynomial.

**Definition 1.2 (Legal positive coordinates).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedArguments`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedArguments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native power-series substitution has arguments [s+x,x,z]. Its coordinates have zero constant coefficient, so it applies to a generally infinite numerator. Conjugation of the accepted outer collision by the label swap 1 and 2 gives the exact signed slice, including negative exponent zeros. This is a native-series substitution only.

**Definition 1.3 (The same infinite numerator).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCollision`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output uses the original P under the lawful native [s+x,x,z] substitution. No new numerator is independently chosen.

**Definition 1.4 (Fixed original third exponent).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedSlice`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After swapping labels 1 and 2, middleNativeSlice fixes the original z exponent. Its bivariate variables are the original first and second coordinates. The collision gives the balanced [s,x,z] coefficient in precisely that order.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedArguments`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCollision`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedCross`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision.balancedSlice`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision](SupportedMiddleCollision.md)
