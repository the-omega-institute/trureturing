# Transport of the original forward kernel

## Abstract

The original complete Chebyshev response has an exact finite signed price-kernel representation.

Write E(t)=psi(t)-t, H(x)=x^(4/5), B(x)=x+H(x), lambda(t)=1/(t*log(t)), and w(t)=(log(t)+1)/(t^2*log(t)^2). The functions H, B, lambda, w, and E are the existing width, endpoint, g, weight, and discrepancy functions. The response is T(x)=sqrt(x)/H(x)^2 times the integral from 0 to H(x) of (E(x+u)-E(x))*w(x+u)/w(x).

**Theorem 1.1 (Existence of the finite response integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x>1 the integrand defining T(x) is interval integrable. Monotonicity makes psi integrable on compact intervals; subtracting the continuous coordinate and multiplying by the continuous weight preserves this property.

**Theorem 1.2 (The complete finite signed price identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_eq_signed_price`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_eq_signed_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x>1, T(x)=sqrt(x)/(w(x)*H(x)^2) times the sum of Lambda(n)*(lambda(n)-lambda(B(x))) over x<n<=B(x), minus the integral from x to B(x) of lambda(t)-lambda(B(x)). The arithmetic sum is written as the difference of two right-closed weighted prefixes. Thus an initial atom is excluded, and a terminal atom has zero price difference. Every prime power carries the full von Mangoldt weight.

The finite arithmetic integration-by-parts identity and its continuous counterpart are applied to the same price curve. Subtracting them produces E(t)-E(x). Translation t=x+u and the exact normalization give the stated original response.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_eq_signed_price`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Transport.forwardResponse_intervalIntegrable`
- Dependency: [D5/S3/Arith/Robin/ActualVonMangoldtBandCompensation](../ActualVonMangoldtBandCompensation.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](../OriginalMovingWindowMoment.md)
