# Inner clearing and supported cancellation

## Abstract

Inner clearing and supported cancellation

**Definition 1.1 (The literal original multiplier).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.innerPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.innerPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplier is x^a0 (x-b-z)^k (x-z)^k b^k (b+z)^a1 z^a2 in the original x,b,z coordinates. Its action is the existing finite Laurent-polynomial convolution.

**Theorem 1.2 (Finite original clearing expansion).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accepted polynomial expansion gives the p,q,h finite action formula on an arbitrary signed coefficient distribution. No support premise is used for multiplication.

**Theorem 1.3 (Reordering coefficient arguments).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reordering the exponent arguments as b,z,x conjugates the literal polynomial action to the rotated multiplier. This is a coordinate reorder on coefficients, with no substitution into an unrestricted distribution.

**Theorem 1.4 (Cancellation in the b-small chamber).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distributions with a uniform lower b bound and, for each b, a lower z bound uniform in x are equal when the original clearing actions agree. Induction in b removes the preceding row of the x-b-z recurrence. The remaining x-z recurrence is cancelled using the current row's own z bound and supported_reconstruction. Finite powers preserve this nested support. Neither a uniform x cutoff nor a global z cutoff is required. Zero exponents and the zero complex algebra remain included.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.innerPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_action_rotate`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.inner_injective`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity](SupportedFinalRInjectivity.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance](ThreeFieldPolynomialCovariance.md)
