# Real-Axis Equations and Gaussian Germ Coefficients

## Abstract

Real-Axis Equations and Gaussian Germ Coefficients

The scalar Euler operator z*deriv multiplies the nth z coefficient by n. An analytic germ which vanishes on a positive real interval vanishes near zero, by isolated zeros. Combining these two facts extracts exact Taylor recurrences from differential equations on such an interval.

For positive r the real radial derivative satisfies 2r*d_r f(sqrt r)=sqrt r*deriv f(sqrt r). The proof uses the square-root derivative only away from zero. The coefficient multiplier after this conversion is the z exponent n, with no additional factor two.

The original-minus-candidate difference uses the full externalT, including the identity pairing. The top theorem assumes boundary-eliminated difference equations explicitly. Deriving them from raw signed equations requires proving that the candidate negative-zero row and column equal the actual nonzero boundaries, then canceling them together with the same source terms. Evenness alone does not justify boundary elimination.

The conclusion gives one complex germ for each pair p,q. It supplies neither a common mode radius, a global identity, nor all signed sectors. It reuses the existing positive parity uniqueness theorem only after deriving both of its coefficient recurrences.

**Theorem 1.1 (hasFPowerSeriesAt_euler_ofScalars).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.hasFPowerSeriesAt_euler_ofScalars`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.hasFPowerSeriesAt_euler_ofScalars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar series for the Euler derivative has coefficient n*a(n), including coefficient zero.

**Theorem 1.2 (analyticAt_eventually_zero_of_pos_real).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.analyticAt_eventually_zero_of_pos_real`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.analyticAt_eventually_zero_of_pos_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zeros on a positive real interval force a complex analytic germ to vanish.

**Theorem 1.3 (linear_euler_germ_coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_euler_germ_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_euler_germ_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A linear Euler differential identity on a positive real interval determines its exact scalar Taylor coefficient equations.

**Theorem 1.4 (two_mul_radial_deriv_eq_euler).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.two_mul_radial_deriv_eq_euler`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.two_mul_radial_deriv_eq_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real radial derivative is converted to the complex Euler derivative at sqrt r for r positive.

**Theorem 1.5 (linear_radial_germ_coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_radial_germ_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_radial_germ_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive real radial identities imply z-Taylor recurrences after shrinking finitely many neighborhoods.

**Theorem 1.6 (externalT_positive_germ_unique_of_pos_real_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.externalT_positive_germ_unique_of_pos_real_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.externalT_positive_germ_unique_of_pos_real_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional positive-sector identification follows from explicitly boundary-eliminated difference equations and evenness, by deriving and reusing the parity coefficient induction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.analyticAt_eventually_zero_of_pos_real`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.externalT_positive_germ_unique_of_pos_real_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.hasFPowerSeriesAt_euler_ofScalars`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_euler_germ_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.linear_radial_germ_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianExternalGermCoefficientBridge.two_mul_radial_deriv_eq_euler`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness](../OriginalGaussianExternalParityUniqueness.md)
