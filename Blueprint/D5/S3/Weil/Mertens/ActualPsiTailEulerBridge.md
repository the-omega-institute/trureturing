# ActualPsiTailEulerBridge

## Abstract

Actual psi-tail calculus and Euler equation

**Theorem 1.1 (Measurable actual psi source).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source qpsi(u)=exp(-u)*(psi(exp u)-exp u) uses the original Chebyshev psi. Measurability is consumed by the generic activated-tail construction in actual_tail_bridge.

**Theorem 1.2 (Unconditional source integrability).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

WeightedPrimeLimit.chebyshev_error_kernel_integrable is transported by x=exp u with its Jacobian to L1 above log 2. This binding helper is consumed by actual_tail_bridge; a uniform bound alone does not establish L1.

**Theorem 1.3 (Actual all-cutoff transform identity).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.Qpsi_eq_Mpsi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.Qpsi_eq_Mpsi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real U and Re s>0, Qpsi(U,s)=-(1+logDeriv(zeta1,1+s))/(1+s)-Apsi(U,s), with Apsi the oriented integral from 0 to U. The proof specializes Mathlib LSeries_eq_mul_integral_of_nonneg to von Mangoldt coefficients using CompleteChebyshevTailIdentity.mangoldt_prefix_bigO, applies exponential substitution and the original ThetaLaplaceContinuation.normalized_logDeriv. It is a consumed binding helper: its germ replaces both Qpsi and its derivative in actual_tail_bridge.

**Theorem 1.4 (Actual signed tail substitution).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.fpsi_eq_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.fpsi_eq_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual fpsi(u)=-Jpsi(exp u) equals minus the tail integral of qpsi(v)*(v+1)/v^2 by integral_comp_exp_Ioi with the original activationDensity and Jacobian. This identity transports the generic tail and transform results to actual_tail_bridge.

**Theorem 1.5 (Actual psi Euler equation and moments).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every U>=log 2, the actual signed psi tail is L1, its transform is analytic for Re s>0, every polynomial moment converges, and the first two transform derivatives equal their actual moment integrals. The Euler expression equals Phi=-Mpsi prime+Mpsi+U^2*fpsi(U)*exp(-sU), with the positive boundary. Its live new inference comes from ActivationTailEuler after same-delivery inlining: triangular absolute Fubini and tail integrability enter the actual tail and the transform estimates. The actual source helpers are proof organization, with no independent escape claim.

The arithmetic application uses only existing source results and the actual Euler synthesis. finiteHead_entire handles Apsi(U,s) as finiteHead(qpsi,0,U) for U>=0 and its negative with endpoints U,0 for U<0. CriticalThetaTailPeak.normalized_zeta_real_ne_zero makes Mpsi analytic at every real x>-1, including zero. For a nontrivial zero rho, factor the normalized zeta at rho using its finite positive analytic multiplicity m, apply ThetaLaplaceContinuation.factor_logDeriv and pole_orders, and set a=rho-1 and Lambda=-m/rho. The regular part is m/(rho*(1+s))-(1+logDeriv(g1,1+s))/(1+s)-Apsi(U,s). This gives the full complex punctured source expansion Lambda/(s-a)+H, order -1, and the derivative-combined order -2. Adding the entire positive boundary gives Phi=Lambda/(s-a)^2+Lambda/(s-a)+J, with the same full complex normalized coefficient for every real U. These binding consequences are applications, not separately retained mathematical declarations. No actual integral convergence for negative Re s, simple-zero condition, or value at 2*rho is assumed.

At U=log 2 the original EulerPoleObstruction.signed_peaks takes the actual L1 tail, this Euler identity, meromorphic forcing and its real corridor. The exact arithmetic identity is ActualThetaTailLaplace.f(u)-fpsi(u)=S(exp u). The single unconditional RHSharpArithmeticEnvelope.S_sub_A_limit gives the vanishing remainder u*exp((1-beta)*u)*(S(exp u)-A(exp u)) for beta>=1/2: the extra exponential is identically 1 at equality and decays above it. The original A is the sqrt-tail integral, not a substitute center. Choosing c<c1<m/(norm(rho)*norm(rho-1)) absorbs the absolute remainder for both real signs s^2=1 and every real late cutoff T. Thus the centered expression u*exp((1-Re rho)*u)*s*(ActualThetaTailLaplace.f(u)-A(exp u)) exceeds c at some u>max(T,log 2), for every nonnegative c below that full multiplicity coefficient. This is a conditional statement about each actual strip zero with Re rho>=1/2; it proves neither RH nor literature novelty and adds no RH, nonresonance, spectral-gap or growth premise.

## References

- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.Qpsi_eq_Mpsi`
- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge`
- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.fpsi_eq_tail`
- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.qpsi_measurable`
- Dependency: [D5/S3/Analytic/Laplace/ActivationTailEuler](../../Analytic/Laplace/ActivationTailEuler.md)
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](../../Arith/Robin/Analytic/RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/ThetaLaplaceContinuation](ThetaLaplaceContinuation.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](WeightedPrimeLimit.md)
