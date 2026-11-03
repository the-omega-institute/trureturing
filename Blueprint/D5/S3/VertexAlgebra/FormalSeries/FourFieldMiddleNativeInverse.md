# FourFieldMiddleNativeInverse

## Abstract

FourFieldMiddleNativeInverse

**Definition 1.1 (Native numerator slices).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.numeratorSlice`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.numeratorSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A generally infinite native four-variable numerator is read into three native cumulative indices, with its fourth total degree kept as a signed parameter. The signed outer numerator coordinate and both unsorted branches are retained.

**Definition 1.2 (The constant-one middle unit).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.middleUnitSeries`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.middleUnitSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With b=STU,y=TU,z=U and outer coordinate one on each total-degree slice, the unit is (1+ST)^a1 (1+ST-T)^k (1-T)^k (1-U-STU)^k (1-U)^k (1-TU)^k. Its constant coefficient is one.

**Definition 1.3 (Native inverse coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.rawMiddleCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.rawMiddleCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse unit multiplies the native numerator slice at total x+b+z+y+sum(a)+6k and is read at b+k,b+y+k+a3,b+y+z+a1+a2+a3+3k. This constructs native series without substituting any unrestricted raw distribution.

**Theorem 1.4 (Actual finite polynomial action).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite variable translations with their total-degree shifts prove that the literal Rmid action on this native inverse recovers the original signed numerator at every four-index target.

**Theorem 1.5 (Derived native support).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native nonnegativity gives nested b,y,z cutoffs. These bounds are properties of the inverse; the actual channel may have arbitrary different nested bounds.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.middleUnitSeries`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.numeratorSlice`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.rawMiddleCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_action`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse.raw_middle_support`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity](SupportedFourFieldMiddleInjectivity.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseCoefficients](ThreeFieldBalancedInverseCoefficients.md)
