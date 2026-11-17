# Exact weighted-tail Fubini transport

## Abstract

Exact weighted-tail Fubini transport

For any real L1 kernel K on (t,infinity), t>=2, set r(t)=(1+log(t))/log(t)^2, density(t)=(log(t)+2)/(t*log(t)^3), Q_K(t)=integral K and I_K(t)=integral K*r. Nonnegative density has total mass r(t). Absolute Fubini on the triangle z<u proves integrability of both weighted kernels and r(t)*Q_K(t)-I_K(t)=integral density(z)*Q_K(z). No differentiability of K or extra weighted-integrability premise is assumed.

Under t=exp(y), the exponential Jacobian cancels exactly the single 1/t in density. The canonical CountableResolvent owns R(y)=(y+1)/y^2 and W(y)=(y+2)/y^3; they are reused here. There is no additional exp(-y) on Q_K(exp(y)). All assertions quantify over analytic families and are not finite computations. The proof uses Mathlib absolute Fubini, improper FTC and exponential substitution; no literature-priority claim is made.

**Theorem 1.1 (Exact weighted-tail Fubini transport).**

Lean statement: `D5/S3/Weil/Mertens/WeightedTailTransport.transport`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailTransport.transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic L1 triangular exchange and both derived integrability claims.

**Theorem 1.2 (Exact weighted-tail Fubini transport).**

Lean statement: `D5/S3/Weil/Mertens/WeightedTailTransport.transport_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedTailTransport.transport_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At this identical y, R(y)*(Q_K(exp(y))-I_K(exp(y))/r(exp(y))) equals integral_(y,infinity) W(v)*Q_K(exp(v)). This identity is consumed by OriginalLocalA; transport_log is not separately exported.

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailTransport.transport`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedTailTransport.transport_exp`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent](IntegratedExplicit/CountableResolvent.md)
