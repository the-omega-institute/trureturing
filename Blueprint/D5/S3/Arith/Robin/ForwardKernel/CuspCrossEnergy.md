# Cusp cross energy

## Abstract

The inner and outer cusp averages have a quadratic logarithmic cross-energy main term.

**Theorem 1.1 (The exact weighted outer integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspAverage_outer_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspAverage_outer_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive h<k, write L=log(k/h). The integral of B_k(y)/y from h to k equals L^2/2-L+2-(L+2)h/k. An elementary logarithmic primitive proves the identity, used to identify the leading cross energy.

**Theorem 1.2 (The cusp cross energy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspCrossEnergy_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspCrossEnergy_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is an absolute positive constant C such that, for h>0 and k>=2h, the absolute difference between the cross energy and h*log(k/h)^2/4 is at most C*h*log(k/h). The proof uses C=10. The intervals below h, between h and k-h, and above k-h are estimated separately. CuspMovingLengths and CommonBandSharpnessTransport consume the uniform bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspAverage_outer_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.cuspCrossEnergy_estimate`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CuspAverages](CuspAverages.md)
