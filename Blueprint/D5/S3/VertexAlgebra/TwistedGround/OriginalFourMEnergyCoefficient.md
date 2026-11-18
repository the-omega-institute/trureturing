# Original fourM total-energy coefficient

## Abstract

OriginalFourMEnergyCoefficient

At total energy E, the source mode is H+K-E-1. Each integral charge q in the specified mod-two coset contributes at charge energy m = (q,q)/2 and oscillator energy E-m. Its charge factor is 16 raised to the power -m. The formal shift by m multiplies the even ordinary sewn coefficients by the m-th power of the square coordinate. The coefficient of index 2(E-m) already contains its ordinary Taylor normalization.

The finite two-index left lowering retains both lowering factorials. Expanding the four external polynomials gives four independent occupation factorials and the two original Laurent selectors. The left sign is the product of the lowering sign with the degree sign from substituting the negative square coordinate.

**Theorem 1.1 (Reflection at the original left Laurent mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.oscillatorKernel_reflected`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.oscillatorKernel_reflected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reflected charge and oscillator polynomial give the same exact left kernel because its Laurent exponent is even. The ground action agrees after reducing the charge modulo two.

**Theorem 1.2 (Evaluation of the reflected half-average).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.cosetKernel_unreflected`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.cosetKernel_unreflected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The average of the original and reflected kernels is evaluated inside the finite energy fiber, with the right leg and the two charge scalars retained.

**Theorem 1.3 (Actual total-energy diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_energy_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_energy_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original scalar on rank-24 homogeneous tensor inputs equals the degree-E coefficient of the negative-coordinate coset series, multiplied in each coset by the two original ground-form coefficients in their original order.

**Theorem 1.4 (Negative intermediate energy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_negative_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_negative_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative charge and oscillator energies make the original intermediate fiber empty and the scalar zero.

**Theorem 1.5 (Left lowering weights and exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.lowered_left_selector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.lowered_left_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each nonzero occupation of a lowered homogeneous tensor factor has doubled weight twice the original weight minus three and minus twice the lowering index. The resulting left exponent satisfies the original Laurent selector throughout the charge sublevel.

**Theorem 1.6 (Right Laurent mode and parity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.right_selector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.right_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an even right weight difference, the selector is one exactly at t = E-1 plus half that difference. For an odd difference it is zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.cosetKernel_unreflected`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_energy_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.fourM_negative_energy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.lowered_left_selector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.oscillatorKernel_reflected`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient.right_selector`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy](../LatticeHalfFockCorrectedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedEnergy](OriginalGaussianFixedEnergy.md)
