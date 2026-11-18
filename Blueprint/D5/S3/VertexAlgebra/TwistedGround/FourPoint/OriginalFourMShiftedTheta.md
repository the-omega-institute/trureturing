# Source transformation

## Abstract

Shifted theta of the original rank-24 charge sectors

**Theorem 1.1 (The quadratic sign).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.quadratic_phase_reduceCharge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.quadratic_phase_reduceCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the class of the original Gram image of an integral charge, the doubled Gram quadratic phase equals the original mod-two quadratic sign.

**Theorem 1.2 (The pairing sign).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.pairing_phase_reduceCharge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.pairing_phase_reduceCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pairing phase of two original Gram images equals the original mod-two Fourier sign.

**Theorem 1.3 (Rank-24 real-source inversion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_real_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_real_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite sum has the original Fourier signs. Its normalization is the inverse of two to the twelfth power times the inverse twelfth power of the period factor. Its inverse source multiplier is the exponential of minus pi times the imaginary unit times the doubled Gram quadratic form divided by the period.

**Theorem 1.4 (The integral charge series).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal sector is the sum over integral charges of the specified reduction. Its quadratic energy is half the original Gram norm and its linear source uses the original Gram form.

**Theorem 1.5 (Forward rank-24 inversion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward law evaluates theta at minus the reciprocal period and the source divided by the period. Its coefficient is the twelfth power of minus the imaginary unit times the period, multiplied by the exponential of the doubled Gram source quadratic and the normalized original finite Fourier transform.

**Theorem 1.6 (Translation of the theta argument).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one to the theta argument leaves the complex source fixed and multiplies the sector by its original quadratic sign.

**Theorem 1.7 (Rank-24 finite Weil relations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.original_finite_weil`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.original_finite_weil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual doubled Gram Fourier operator squares to the identity, and its composite with the quadratic phase operator cubes to the identity.

**Theorem 1.8 (Source multipliers of the B and D charts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chart_source_multipliers`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chart_source_multipliers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each chart source the forward exponential from theta inversion equals the exponential of half the complementary covariance discrepancy times the original Gram quadratic of that chart's source vector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_real_S`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chart_source_multipliers`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.original_finite_weil`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.pairing_phase_reduceCharge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.quadratic_phase_reduceCharge`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta](../../Characters/LatticeDiscriminantShiftedTheta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](../../LatticeHalfFockChargedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge](OriginalFourMDiscriminantCharge.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource](OriginalFourMPeriodSource.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](../OriginalFourMChargeCoset.md)
