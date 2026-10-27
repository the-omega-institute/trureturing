# Signed native monomial multiplication

## Abstract

Signed native monomial multiplication

**Definition 1.1 (finalSlice).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.finalSlice`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.finalSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix the signed third coefficient before the final bivariate native shear.

**Theorem 1.2 (signed_final_transform).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_final_transform`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_final_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final signed collision transform equals the native final shear. The common native coefficients imply the actual lower support used in the finite sum.

**Theorem 1.3 (signed_extra_mul).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_extra_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_extra_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by (X0+X1)^A X1^B is the finite signed binomial translation on every exponent.

**Theorem 1.4 (remove_supported_extra).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.remove_supported_extra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.remove_supported_extra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual uniform first-coordinate lower bound licenses the supported positive inverse and cancels the temporary extra factor. The third coordinate remains unrestricted.

**Definition 1.5 (signedExtension).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signedExtension`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signedExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signed extension is a complex-linear map from native series to signed coefficient distributions.

**Theorem 1.6 (signed_X_pow_mul).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_X_pow_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_X_pow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of a native series by X_i^n subtracts n in signed coordinate i. This identity holds at every signed exponent, including the zero branches caused by a negative target or an insufficient monomial degree.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.finalSlice`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.remove_supported_extra`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signedExtension`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_X_pow_mul`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_extra_mul`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_final_transform`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber](ThreeFieldFinalLaurentFiber.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance](ThreeFieldPolynomialCovariance.md)
