# The actual theta tail and a strict Robin response

## Abstract

The actual weighted Chebyshev theta tail equals the normalized second Mertens error and gives an explicit prefix-lcm Robin response.

**Theorem 1.1 (The improper integral and its arithmetic consequence).**

Lean statement: `D5/S3/Arith/Robin/ThetaTailRobinWitness.theta_tail_mertens_robin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ThetaTailRobinWitness.theta_tail_mertens_robin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=2 the actual function (theta(t)-t)*w(t), where w(t)=(log(t)+1)/(t²*log(t)²), is Lebesgue integrable on (x,infinity). Its negative integral is E₂p(x)-(theta(x)-x)/(x*log(x)). Here theta is the Chebyshev prime sum and E₂p is the second Mertens error with Mertens.M as its constant.

Write I(x)=(theta(x)-x)/(x*log(x))-E₂p(x). Classical finite Abel summation gives I(u)=I(x)-integral_x^u (theta(t)-t)*w(t) dt. The finite calculation reuses the canonical ThetaTailPartialSummation.theta_tail_finite supplier from MertensCumulativePeak; its reciprocal logarithmic weight and prime-cutoff identities provide the finite bridge. The elementary bound 0<=theta(u)<=u*log(4), together with |E₂p(u)|<=(log(4)+6+Mertens.E₁)/log(u), proves I(u) tends to zero. ActualThetaTailLaplace supplies unconditional integrability of the same actual kernel. Taking the upper limit to infinity therefore fixes the normalization and proves the equality.

For x>=10000, suppose this negative integral exceeds 7/sqrt(x). The Mertens correction E₃(x)+E₂p(x) has absolute value at most 4/x<=1/sqrt(x), and (psi(x)-theta(x))/(x*log(x))<=2/sqrt(x). These bounds give E₃(x)<-4/sqrt(x)-(psi(x)-x)/(x*log(x)). The common prefix-lcm response in LcmRobinResponse applies at this same real x.

The resulting integer is exactly D=lcm(1,...,floor(x)). It satisfies D>5040, sigma(D)/D>exp(gamma)*log(log(D)), log(D)=psi(x), and D<=exp(x*log(x)), where gamma is the real Euler constant. This theorem takes the stated actual tail peak as a premise; the following application supplies it conditionally from a genuine zeta zero.

Suppose rho is a complex number with zeta(rho)=0 and 1/2<beta=Re(rho)<1. Then for every natural number B there is a real x>=10000 such that the actual integer D=lcm(1,...,floor(x)) satisfies B<D, 5040<D, sigma(D)/D>exp(gamma)*log(log(D)), log(D)=psi(x), and D<=exp(x*log(x)). This is an application of CriticalThetaTailPeak.critical_theta_tail_peak, ActualThetaTailLaplace.actual_theta_tail_laplace_ode and the arithmetic theorem above, with the same actual theta tail and the same prefix-lcm integer throughout.

To derive the application, let m be analyticOrderNatAt(zeta,rho) and A=m/(norm(rho)*norm(rho-1)). The critical peak theorem gives m>0; the real-part bounds exclude rho=0 and rho=1, so A>0. Set c=A/2 and delta=beta-1/2>0. The Mathlib limit tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero at exponent one gives 7*u*exp(-delta*u) tending to zero. Choose a threshold beyond which this quantity is less than c, and choose U also beyond 1, log(10000) and log(B+1). The genuine-zero critical peak theorem supplies u>max(U,log(2)) with c<u*exp((1-beta)*u)*f(u). Since u*exp((1-beta)*u)>0 and its product with 7*exp(-u/2) is exactly 7*u*exp(-delta*u), this forces f(u)>7*exp(-u/2). The actual change-of-variables identity f(u)=F(exp(u)), where F is the negative weighted theta integral, and sqrt(exp(u))=exp(u/2) give F(x)>7/sqrt(x) at x=exp(u)>=10000. The theorem above now gives the strict Robin inequality, exact logarithm and original size bound at this x.

The choice x>=B+1 gives B+1<=floor(x). For n=floor(x)>=1, Chebyshev.choose_dvd_lcmUpto gives n dividing lcmUpto(n); positivity of lcmUpto(n) then gives n<=D, hence B<D. Thus the conditional conclusion concerns unbounded genuine integers, without an additional assumed tail peak. It does not establish the existence of an off-line zero, RH, an actual numerical Robin counterexample, or an effective cutoff or location for these witnesses.

## References

- Truth anchor: `D5/S3/Arith/Robin/ThetaTailRobinWitness.theta_tail_mertens_robin`
- Dependency: [D5/S3/Arith/Robin/MertensCumulativePeak](MertensCumulativePeak.md)
- Dependency: [D5/S3/Weil/Mertens/ActualThetaTailLaplace](../../Weil/Mertens/ActualThetaTailLaplace.md)
