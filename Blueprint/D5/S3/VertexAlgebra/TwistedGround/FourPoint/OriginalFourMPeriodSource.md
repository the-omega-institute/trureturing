# The Euler periods and spatial covariance

## Abstract

The original four-point covariance on the period lips

The native periods in A, B and D have arguments 1-1/z, z and 1/z for 0<z<1. The Pfaff intermediate argument is 1-z. An upper approach of the A parameter pairs with a lower approach of D.

**Theorem 1.1 (Differentiated Pfaff identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set C(r)=r*(1-r)*P'(r)/P(r) for the Euler slit period. Differentiating P(r/(r-1))=sqrt(1-r)*P(r) gives C(r/(r-1))=C(r)/(1-r)-r/(2*(1-r)) throughout the open slit domain.

**Theorem 1.2 (The correction at the Pfaff intermediate chart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At r_A=1-1/z the differentiated Pfaff identity gives z*C(r_A)+(1-z)/2=C(1-z). Both arguments are interior to the slit domain of P.

**Theorem 1.3 (The A period root).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive real cross-ratio interval, the chosen A root is the reciprocal of sqrt(z) and multiplies P(r_A) to give P(1-z).

**Theorem 1.4 (The D periods on the two open half-planes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the native D argument t the continued period is (tau(1-1/t)+s)*P(1-t)/i. The sign s is +1 on the D lower half-plane and -1 on the D upper half-plane. The Pfaff jump of tau at 1-t gives exact agreement with the slit integral on each half-plane.

**Theorem 1.5 (Boundary values in the native D argument).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each real t>1, the explicit D period and its complex derivative are the two limits from the matching open lip. Analyticity of the explicit continuation at t transfers the derivative because the periods agree on the adjacent open half-plane.

**Theorem 1.6 (The chosen root on the D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The principal square root of 1-r_D limits to i*sqrt(1-z)/sqrt(z) when r_D approaches 1/z from below. The upper lip has the negative of that root.

**Theorem 1.7 (The two complementary Wronskians).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pulled-back A kernel minus the new kernel is 1/(pi*P(1-z)*P(z)) in B units and 1/(pi*P(r_A)*P_D(r_D)) in D units. The first value follows from the Pfaff correction. The second takes the limit of the complementary Wronskian with P_D and its derivative on the matched lip.

**Theorem 1.8 (The source coefficient in the shifted theta exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the new Gram source M and the complementary periods p and q, the forward multiplier exponent is the Gram square of M divided by 2*pi*p*q. The Pfaff intermediate source acquires the phase -i from the A root and the B lift, and the D comparison uses the phase i. The inverse multiplier has the negative exponent.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialPfaffNome](../../../Analytic/OriginalHalfBinomialPfaffNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart](../OriginalFourMActualChart.md)
