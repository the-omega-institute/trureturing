# Normal Convergence of the Original Four-Point Charge Sum

## Abstract

Normal convergence of the original fixed four-point occupation over charges.

**Theorem 1.1 (Summable compact majorant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.compact_charge_normal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.compact_charge_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the compact external labels and occupation of the four-point energy coefficient. On a compact chart, the scalar and covariance are bounded. The signed mean grows linearly in the charge size. The finite native affine coefficient has charge growth bounded by an occupation-dependent power. The original nome to the exact charge energy makes that bound summable, and the charge sum is holomorphic in the interior.

**Theorem 1.2 (Original sewn terms near zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_normal_at_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_normal_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the sewing coordinate z, the source scalar, energy shift, and two charge factors give Q₀(z²) to the charge energy. The affine coefficient retains the literal signed mean and sewn covariance. A closed disk about zero admits a summable bound for every charge and the resulting sum is holomorphic on its interior.

**Theorem 1.3 (Charge-class Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order 2E in the sewing coordinate, local uniform convergence permits the Taylor coefficient to pass through the charge sum. Only charges of energy at most E contribute. Each surviving coefficient is the degree-E coefficient of the original square-coordinate charge series in that charge class.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.compact_charge_normal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeNormal.sewn_charge_normal_at_zero`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialNome](../../Analytic/OriginalHalfBinomialNome.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop](../Sewing/CanonicalFullChargeLoop.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum](FiniteSqueezedVacuum.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient](OriginalFourMEnergyCoefficient.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial](OriginalGaussianExternalRadial.md)
