# The complete forward Mellin adjoint

## Abstract

Absolute Fubini retains every complete-prime-power contribution in the forward Mellin adjoint.

**Theorem 1.1 (Absolute transport of the complete signed response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Fubini.unbounded_forward_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Fubini.unbounded_forward_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x0>=4 and let f be a measurable complex center weight. Assume that norm(f(x))*abs(T(x)) and norm(f(x))*V(x) are integrable over x>=x0, where V(x)=integral k(x,t) dt is the original continuous kernel mass. Then the literal adjoint integral of f(x)*k(x,t) is integrable in t, and its Lambda-weighted positive-integer values form an absolutely summable series.

The integral of f(x)*T(x) equals that series minus the integral of the adjoint in t. Nonnegativity of the original kernel bounds its complete arithmetic row mass by abs(T(x))+V(x). This proves both product-integrability statements before either use of Fubini. Every prime power keeps its full log-prime weight.

**Theorem 1.2 (Signed adjoint truncations recover the Mellin integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Fubini.forwardMellin_adjoint_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Fubini.forwardMellin_adjoint_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume alpha>=0 and an eventual power bound abs(psi(t)-t)<=C*t^alpha for all t>=t0. For x0>=4 and Re(s)>max(1/2,alpha-3/10), the actual adjoint q_s(t) is integrable over t>1. The difference between the sum of Lambda(n)*q_s(n) for 0<=n<=floor(b) and the integral of q_s(t) from 1 to b tends to the original forward Mellin integral as b tends to infinity.

The established response convergence and continuous-kernel moment bound supply the two absolute majorants. The adjoint vanishes for t<=1. Absolute summability gives the arithmetic truncation limit, and integrability gives the continuous truncation limit. The power error estimate is an explicit hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Fubini.forwardMellin_adjoint_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Fubini.unbounded_forward_adjoint`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Adjoint](Adjoint.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinConvergence](MellinConvergence.md)
