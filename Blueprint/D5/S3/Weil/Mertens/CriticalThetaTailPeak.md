# Critical Theta Tail Peaks

## Abstract

Critical-exponent positive peaks of the signed activation-weighted theta tail.

**Theorem 1.1 (An explicit amplitude for every genuine zero).**

Lean statement: `D5/S3/Weil/Mertens/CriticalThetaTailPeak.critical_theta_tail_peak`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CriticalThetaTailPeak.critical_theta_tail_peak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a genuine zero of Riemann zeta with one half < Re(rho) < one. Write beta=Re(rho), sigma=beta-1 and m for its analytic multiplicity. The multiplicity is positive and Im(rho) is nonzero. For every real c with 0 <= c < m/(norm(rho) norm(rho-1)) and every real T, there is u > max(T,log 2) such that c < u exp((1-beta)u) f(u). Here f is the actual signed tail from ActualThetaTailLaplace, using the reciprocal logarithmic activation density; it equals the original tail F(exp u) at every real u.

Suppose instead that the indicated normalized tail is eventually at most c. At one positive cutoff U, put h(u)=c exp(sigma u)/u and g=h-f on u>U. Actual integrability of f and exponential decay of h make g an integrable nonnegative density, hence a finite positive measure. Its actual Laplace transform G is a complex moment-generating function. Its comparison transform K is the actual transform of h. Genuine differentiation gives K'(z)=-c exp(-(z-sigma)U)/(z-sigma) and K''(z)=c exp(-(z-sigma)U)(1/(z-sigma)^2+U/(z-sigma)). For c>0, K itself has a logarithmic boundary singularity; for c=0, K=0. In neither case is a meromorphic extension of K across sigma presumed.

The actual signed theta transform L satisfies the Euler equation zL''+2L'=T+B on the positive half-plane, where T=-M'+M and B=U^2 f(U) exp(-zU). Consequently G=K-L has meromorphic Euler forcing P-T-B, where P is the explicit Euler image of K. This forcing is regular at every real point strictly to the right of sigma. PositiveEulerContinuation therefore gives actual exponential integrability throughout Re(z)>sigma. Subtracting the weighted integrable densities h and g gives weighted absolute integrability of the actual signed tail there, and L=K-G is holomorphic on that half-plane.

The normalized-zeta formula and the positive-real sign of zeta make T+B holomorphic at the real point sigma. EulerLocalContinuation extends the signed solution L across sigma on a full complex disk. Its first two derivatives are consequently bounded along sigma+epsilon as epsilon decreases to zero. The explicit derivatives of K then give epsilon^2 times the first positive moment tending to zero and epsilon^2 times the second positive moment tending to c. No boundary convergence of the signed integral or of positive moments is presumed.

At the nonreal point a=rho-1 the exact double-pole coefficient of T is -m/rho. P and B are regular there. A punctured neighborhood of that selected pole, together with the Euler identity at its regular points, gives epsilon^2 (zG''+2G')(a+epsilon) tending to m/rho. Positivity of the genuine moment integrals gives norm(G'(x+i gamma)) <= -G'(x) and norm(G''(x+i gamma)) <= G''(x). Their real limits imply m/norm(rho) <= norm(rho-1)c, contradicting the assumed strict coefficient bound. No rightmost-zero hypothesis is needed.

Taking c to be half the positive amplitude supplies conditional arbitrarily late peaks. Since exp((beta-one half)u)/u tends to infinity, these eventually cross an envelope of the form 7 exp(-u/2). An arithmetic bridge from that envelope to actual prefix least-common-multiple Robin violations is a separate requirement. This theorem does not assert an off-line zero, the Riemann hypothesis, an unconditional violating integer, an effective peak location, an endpoint beta=one half or beta=one, or a peak strictly above the limiting amplitude. The argument uses classical positive Laplace continuation and local pole comparison; no literature originality is asserted.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CriticalThetaTailPeak.critical_theta_tail_peak`
- Dependency: [D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign](../../Analytic/Isolation/RiemannZetaPositiveRealSign.md)
- Dependency: [D5/S3/Analytic/Laplace/PositiveEulerContinuation](../../Analytic/Laplace/PositiveEulerContinuation.md)
- Dependency: [D5/S3/Weil/Mertens/ActualThetaTailLaplace](ActualThetaTailLaplace.md)
