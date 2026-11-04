# The native chart and its unit

## Abstract

The native chart and its unit

**Definition 1.1 (FinalCone).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.FinalCone`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.FinalCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three cumulative signed coordinates are nonnegative; no positivity of individual raw exponents is imposed.

**Definition 1.2 (decode).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.decode`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n in natural three-space, the signed raw exponent is (n0-k,n1-n0-2k,n2-n1-a0-a1-a2). No sortedness of n is required.

**Definition 1.3 (coneEquiv).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.coneEquiv`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.coneEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cumulative coordinates give a bijection from FinalCone to all natural three-space. Conversion to natural numbers occurs after proving nonnegativity.

**Theorem 1.4 (old_zero_outside).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_zero_outside`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_zero_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Laurent expression vanishes outside FinalCone by its signed exponent balances.

**Definition 1.5 (nativeChart).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.nativeChart`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.nativeChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at (r,s,t) is the numerator coefficient at (r,s-r,t-s) when r<=s<=t, and zero otherwise.

**Theorem 1.6 (old_coefficient_chart_sum).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_coefficient_chart_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_coefficient_chart_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every decoded native index, the Laurent coefficient is the sum on its original finite fiber of the weights times the nativeChart coefficient at (n0-j-h,n1-q-l,n2).

**Theorem 1.7 (native_chart_factorization).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_chart_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_chart_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under x=XYZ,y=YZ,z=Z, the literal six factors x^k y^k (x+y)^k (x+y+z)^A (y+z)^C z^D factor as X^k Y^(3k) Z^(3k+A+C+D) times (1+X)^k (1+Y+XY)^A (1+Y)^C in every commutative ring.

**Definition 1.8 (chartUnitSeries).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnitSeries`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnitSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product (1+X)^k (1+Y+XY)^a0 (1+Y)^a1 has constant coefficient one.

**Definition 1.9 (chartUnit).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnit`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This series is a unit over any commutative ring, with inverse supplied by MvPowerSeries.invOfUnit.

**Theorem 1.10 (native_unit_equation).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_unit_equation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_unit_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the unit series by its inverse times nativeChart P returns nativeChart P for every formal series P.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.FinalCone`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnit`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.chartUnitSeries`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.coneEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.decode`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.nativeChart`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_chart_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.native_unit_equation`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_coefficient_chart_sum`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone.old_zero_outside`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber](ThreeFieldFinalLaurentFiber.md)
