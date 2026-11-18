# Horizontal squared-log potential

## Abstract

The horizontal squared-log potential transports exactly through the singular height, with a uniform 2*pi height bound.

For real a<=b and arbitrary real beta, put L(t)=integral from a to b of log((x-beta)^2+t^2). The real kernel is 2*t/((x-beta)^2+t^2), with ordinary Lean division. At t=0 it is zero at every x, including x=beta. The logarithm is interval integrable even at a zero inside the segment or at either endpoint, by Mathlib's meromorphic logarithm theorem.

**Theorem 1.1 (Signed transport across every pair of heights).**

Lean statement: `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_signed_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_signed_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u and v, L(v)-L(u) equals the integral from u to v of the horizontal real kernel integral. The proof evaluates L(t) as the endpoint difference of P(y,t)=y*log(y^2+t^2)-2*y+2*t*arctan(y/t), with y=x-beta. At t=0, Real.log_pow and the all-endpoint integral_log give the same formula without a spatial split. The bounded arctangent factor proves continuity at zero. Away from zero the height derivative of P is 2*arctan(y/t). FTC on each closed half-line and signed adjacent interval addition give the exact all-domain identity.

**Theorem 1.2 (The uniform 2*pi height bound).**

Lean statement: `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u and v, abs(L(v)-L(u))<=2*pi*abs(v-u). Mathlib's integral_div_sq_add_sq evaluates the horizontal kernel as 2*(arctan((b-beta)/t)-arctan((a-beta)/t)), also at t=0. The arctangent range gives its absolute bound 2*pi, which is integrated along the exact transport formula. The quantifiers include a=b, beta inside or outside the segment or at an endpoint, u=0, v=0 and opposite signs. No derivative at zero is asserted.

The elementary integrability, arctangent evaluation, primitive derivatives and norm estimate are consumed analytic helpers. The substantive inference is transport of the actual logarithmic integral through the singular ordinate. This scalar theorem does not prove generic holomorphic transport, the actual zeta J/S bridge or RH. At a zero ordinate a later bridge must integrate the real or imaginary part first; this result does not justify a complex log-derivative integral.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_lipschitz`
- Truth anchor: `D5/S3/Analytic/Boundary/HorizontalLogPotential.logPotential_signed_transport`
