# Native Chosen-Tensor Charged Field Hermitian Adjoints

## Abstract

Native Chosen-Tensor Charged Field Hermitian Adjoints

The carrier is the literal ActualTensor(D,hu) with its unchanged nested chosen ActualGround, groundRepresentation and groundAction. The form is exactly the original tensorForm. The chargedCoefficient retains chargeScalar(D,a)=2^(-bilinear(D,a,a)), not a modified normalization. Conjugation fixes this real integral power, and replacing a by -a leaves it unchanged. The original chosen-ground signed adjoint is reused with the exact epsilon(D,a,a); group inverse is not silently identified with literal charge reflection.

**Theorem 1.1 (Actual Coefficient and Actual Existing Field).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian.charged_coefficient_field_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian.charged_coefficient_field_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice D, determinant unit proof hu, integral charge a, integer exponent M and arbitrary original tensor states v,w, tensorForm(chargedCoefficient(a,M)v,w) equals epsilon(D,a,a) times tensorForm(v,chargedCoefficient(-a,-M-2*chargeNorm(D,a))w). The theorem also states and proves the same identity for the literal existing chargedField.coeff on all targets and all coefficient exponents. There is no replacement field. On pure tensors, the proved full oscillator coefficient transpose and the original chosen-ground signed adjoint combine with the real chargeScalar. Independent tensor induction in both arguments then proves the law for arbitrary mixed finite tensors, not only separable states. The chargedField clause consumes the resulting operator law through the original HVertexOperator coefficient identity.

The theorem gives the adjoint both for the native charged coefficient and for the corresponding coefficient of the original field. The tensor extension uses the original oscillator transpose, the signed ground adjoint and the real charge scalar, which is invariant under charge reflection. The result includes rank zero and indefinite signature wherever the Gram determinant is a unit.

The adjoint concerns the original charged field on the chosen tensor carrier. The all-state twisted Jacobi, gluing and fusion questions remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian.charged_coefficient_field_adjoint`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint](LatticeHalfFockConvolutionAdjoint.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian](LatticeHalfFockTensorHermitian.md)
