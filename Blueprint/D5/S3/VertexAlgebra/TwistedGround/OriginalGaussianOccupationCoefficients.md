# Ordinary energy coefficients of the literal occupation germ

## Abstract

OriginalGaussianOccupationCoefficients

At each fixed frequency cutoff, the actual occupation germ converges normally on a positive closed source disk times both external unit polydisks. Exact source scaling turns each summand into a monomial at twice the positive internal energy. Locally uniform derivative convergence at every finite order justifies source extraction. The existing oscillator-energy finiteness theorem makes its energy layer finite. The resulting coefficient is iteratedDeriv at order 2*n divided by (2*n)!, including n=0. No cutoff-independent raw radius is used. The original Wick readout has a common-box energy-layer expression. Its external analytic coefficient identification remains separate.

**Theorem 1.1 (Finite internal energy layer).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.energy_layer_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.energy_layer_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strictly positive ordinary frequencies make every fixed energy layer finite, including the zero layer and empty internal index types.

**Theorem 1.2 (Holomorphic finite partial derivatives).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.iterated_partial_diff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.iterated_partial_diff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite partial sum of entire source summands has differentiable iterated source derivatives.

**Theorem 1.3 (Literal finite effective exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_mixed_exponent_collect`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_mixed_exponent_collect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic expression in the two mixed original means collects into the finite effective charge constant, the actual ordered effective covariance and the actual effective mean. Symmetry of the full insertion covariance identifies the two linear cross terms. Products use ordinary transpose, with no conjugation or extra charge half.

**Theorem 1.4 (Source coefficient of the literal finite effective generating function).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_sewing_energy_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_sewing_energy_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite energy layer is the 2*n ordinary source coefficient after collecting the actual finite constant, effective covariance and effective mean. The two external variable families remain arbitrary in their unit polydisks. External coefficient extraction and its exchange with source differentiation remain unproved.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.energy_layer_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.iterated_partial_diff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_mixed_exponent_collect`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients.original_finite_sewing_energy_coefficient`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic](OriginalGaussianSewnAnalytic.md)
