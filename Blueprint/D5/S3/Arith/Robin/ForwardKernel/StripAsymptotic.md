# Strip estimates for the forward adjoint

## Abstract

Polynomial bounds for the forward adjoint on a vertical strip.

**Theorem 1.1 (The inverse coordinate scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.coordinate_power_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.coordinate_power_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>=2 and z in [0,1], the inverse coordinate satisfies x(t,z)^(-1/5)<=2*t^(-1/5).

**Theorem 1.2 (The unit square has area one).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.unitSquare_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.unitSquare_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real Lebesgue measure of [0,1] times [0,1] is one.

**Theorem 1.3 (The triangular principal coefficient).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.triangle_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.triangle_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral over the unit square of the indicator of z<=u, with constant complex value one, is one half.

**Theorem 1.4 (Uniform relative powers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.normalizedPower_strip_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.normalizedPower_strip_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a positive absolute constant C such that, for -1/5<=Re(s)<=1, t>=2 and 0<=z<=1, the relative power P=exp((-s-1/2)*log(x(t,z)/t)) has norm at most C, its difference from one has norm at most C*(1+|s|)*t^(-1/5), and its time derivative has norm at most C*(1+|s|)*t^(-6/5). The logarithm is real, so the exponential norm depends only on Re(s). The mean value inequality along the exponential segment bounds its difference from one.

**Theorem 1.5 (Polynomial remainder bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.adjointRemainder_strip_C1_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.adjointRemainder_strip_C1_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a positive absolute constant C such that, for -1/5<=Re(s)<=1 and t>8, the exact adjoint remainder r_s(t) satisfies |r_s(t)|<=C*(1+|s|)*t^(-Re(s)-7/10) and |r_s'(t)|<=C*(1+|s|)^2*t^(-Re(s)-17/10). The relative power estimates combine with the weight ratio and inverse Jacobian bounds on the fixed triangle 0<=z<=u<=1. Its area is one half. Differentiating the principal Mellin power supplies the second parameter factor.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.coordinate_power_one`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.triangle_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.unitSquare_volume`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.adjointRemainder_strip_C1_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.normalizedPower_strip_bounds`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Asymptotic](Asymptotic.md)
