# The independent inclusive original J identity

## Abstract

The independent inclusive original J identity

Absolute-continuity calculus, interval integration, von Mangoldt arithmetic and Euler normalization are imported from the pinned Apache-2.0 Mathlib. Finite indicator-tail summation and its application to this independently defined J are repository derivations; no RH or sign estimate is a premise.

**Theorem 1.1 (Finite Abel summation for an absolutely continuous function).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.finite_abel_ac`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.finite_abel_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite index set, real weights w, knots k in [0,D], gamma, D>=0 and absolutely continuous H, finiteB(t)=gamma-t+sum_{k_i<=t} w_i. The exact identity is sum_i w_i*H(k_i)-integral_0^D H-(gamma-D+sum_i w_i)*H(D)=-gamma*H(0)-integral_0^D finiteB(t)*deriv(H)(t). Integrating each inclusive tail indicator supplies the knot contribution. Empty sets, knots at D and D=0 are included.

**Theorem 1.2 (The inclusive prime-power identity).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.original_J_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.original_J_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff is all natural numbers from 2 through floor(exp(D)), inclusive; b(t)=EulerGamma-t+sum_{n<=exp(t)} vonMangoldt(n)/n. Independently, J(D,f,fprime)=2*integral_0^D b(t)*exp(t/2)*(fprime(t)+f(t)/2). Assuming D>=0, absolute continuity of f and actual a.e. derivatives fprime, the identity is 2*sum_{n in cutoff(D)} vonMangoldt(n)/sqrt(n)*f(log(n))-2*integral_0^D exp(t/2)*f(t)-2*b(D)*exp(D/2)*f(D)=-2*EulerGamma*f(0)-J(D,f,fprime). The weighted lift H(t)=exp(t/2)*f(t) supplies both the integral and endpoint terms.

**Theorem 1.3 (The conditional endpoint substitution).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.fullR_eq_original_J`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.fullR_eq_original_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The definition fullR(D,Z,f) retains the same prime-power sum and continuum integral, with endpoint term b(D)*Z/2. Substituting f(D)=-exp(-D/2)*Z/4 yields fullR(D,Z,f)=-2*EulerGamma*f(0)-J(D,f,fprime). This supplier explicitly assumes that endpoint equality; OriginalActualSpectralEndpoint proves it for the actual test and consumes this theorem.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.finite_abel_ac`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.fullR_eq_original_J`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.original_J_identity`
