# The forward adjoint remainder

## Abstract

The inverse-coordinate forward adjoint has an exact triangular main coefficient and a uniform C1 remainder.

Use x(t,z) determined by t=x+z*x^(4/5), J(t,z)=1/(1+(4/5)*z*x(t,z)^(-1/5)), A(x,u)=w(x+u*x^(4/5))/w(x), and P(t,z,s)=exp((-s-1/2)*log(x(t,z)/t)). The normalized coefficient is the integral of P*A*J on the fixed triangle 0<=z<=u<=1. The area of that triangle is exactly 1/2.

**Theorem 1.1 (Correlated control of the integrand and its derivative).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.normalizedBody_C1_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.normalizedBody_C1_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>=8 and z,u in [0,1], the coefficient P*A*J is differentiable in t. With p=-s-1/2 and C(s)=(2*|p|+50)*exp(2*|p|)+10, its difference from one has norm at most C(s)*t^(-1/5), and its time derivative has norm at most C(s)*t^(-6/5). The derivative of the ratio A uses the same moving center in numerator and denominator.

**Theorem 1.2 (The exact inverse-coordinate integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_eq_iterated`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_eq_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse-coordinate adjoint is t^(-s-1/2) times the normalized triangular coefficient. Fubini and the identity t^(-s-1/2)*P=x(t,z)^(-s-1/2) identify it with the integral over 0<=z<=1 of x(t,z)^(-s-1/2)*integral_z^1 A(x(t,z),u) du divided by 1+(4/5)*z*x(t,z)^(-1/5).

**Theorem 1.3 (Uniform C1 control after subtracting the principal term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_uniform_C1_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_uniform_C1_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r_s(t)=t^(-s-1/2)*(normalizedAdjoint(t,s)-1/2). For every compact K in the complex plane there is C_K>0 such that, for s in K and t>8, |r_s(t)|<=C_K*t^(-Re(s)-1/2)*t^(-1/5) and |d_t r_s(t)|<=C_K*t^(-Re(s)-3/2)*t^(-1/5).

The derivative passes under an integral on a fixed compact triangle. Both the normalized coefficient and its derivative have uniform bounds there. The product rule is applied only after subtracting the exact coefficient 1/2. Local boundedness of the explicit parameter constants then gives the compact uniform estimates.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_eq_iterated`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.inverseAdjoint_uniform_C1_remainder`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Asymptotic.normalizedBody_C1_estimate`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Remainder](Remainder.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
