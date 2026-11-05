# The actual six-factor Laurent action

## Abstract

The actual six-factor Laurent action

**Theorem 1.1 (raw_R_action_transport).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction.raw_R_action_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction.raw_R_action_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative complex algebra R, every generally infinite three-variable formal series P, all natural k and a, and every signed exponent e, the finite polynomialAction of x^k y^k (x+y)^k (x+y+z)^a0 (y+z)^a1 z^a2 on laurentCoefficient P k a equals signedExtend P e. Monomial actions become multiplication by XYZ,YZ,Z in the native chart. Finite addition, multiplication and powers transport the literal six factors. Removing their native monomial shift leaves W(e)=(e0,e0+e1,e0+e1+e2); a negative W coordinate vanishes, and a negative raw coordinate with nonnegative W gives an unsorted native index. Zero exponents and the zero algebra remain included. This algebraic statement supplies no channel identification, convergence, sewing or vertex-algebra completion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction.raw_R_action_transport`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance](SupportedFinalCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients](ThreeFieldFinalInverseCoefficients.md)
