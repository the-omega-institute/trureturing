# The finite raw inner fiber

## Abstract

The finite raw inner fiber

**Definition 1.1 (Signed numerator input).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerInput`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonnegative r,j,l the numerator exponents are (x+a0+2k+r+j,b+k-r-l,z+a1+a2-j+l). The coefficients may be requested at arbitrary signed x,b,z.

**Definition 1.2 (Integer-binomial weights).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerWeight`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar is (-1)^(r+j) binom(-k,r) binom(-(2k+r),j) binom(-a1,l), using the inherited integer upper-index convention.

**Theorem 1.3 (Nonrectangular bounds).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.inner_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.inner_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity of all three numerator exponents implies r+l <= b+k and r+j <= b+z+k+a1+a2, and nonnegativity of the total shifted exponent. These bounds are proved before taking toNat.

**Theorem 1.4 (An exact finite fiber).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.mem_innerFiber_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.mem_innerFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite containing box r,l <= (b+k).toNat and j <= (b+z+k+a1+a2).toNat is filtered by all three signed numerator constraints. Membership is equivalent to precisely those constraints. In particular, negative bounds introduce no spurious terms; P need not have finite support.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerInput`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.innerWeight`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.inner_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber.mem_innerFiber_iff`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision](SupportedThreeFieldCollision.md)
