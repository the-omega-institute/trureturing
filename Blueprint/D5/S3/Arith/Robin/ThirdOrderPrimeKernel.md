# A Cubic Approximation of the Actual First-Clock Kernel

## Abstract

A cubic price approximation retains the complete three-term center and bounds the actual-prime centered error on the unchanged original selected domain.

The cubic approximation retains the original selected domain and clocks. The external prime-mass bound and both response-integrability premises remain explicit. The one public theorem is complete_selected_actual_prime_error; the derivative, remainder and centering calculations are private suppliers used in its proof.

**Theorem 1.1 (The complete original selected domain retains an absolute error budget).**

Lean statement: `D5/S3/Arith/Robin/ThirdOrderPrimeKernel.complete_selected_actual_prime_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ThirdOrderPrimeKernel.complete_selected_actual_prime_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take OriginalFirstClockTransport.OriginalWindow X and OriginalBounds X ell R with ell>=243. Put S=selectedDomain X and M=(volume S).toReal. This is the union of every original good consecutive-label closed edge, with overlaps counted once. The labels remain the complete original window, the sources are the least full-domain maximizers over positive multiples of 5040p, and each good edge retains its complete strict inventory. The bounds do not filter edges, and S is not shortened.

Use the existing price lambda(t)=1/(t log(t)) and activationDensity w(t)=(log(t)+1)/(t^2 log(t)^2). Set H=t^(4/5), d=t^(11/10). At offset 0<=u<=H the literal price-difference kernel is k_t(t+u)=[lambda(t+u)-lambda(t+H)]/[w(t)d]. Its cubic price approximation is P3_t(t+u)=d^(-1)[H-u+(w'(t)/(2w(t)))(H^2-u^2) +(w''(t)/(6w(t)))(H^3-u^3)]. Both use the same window and the actual first clocks.

The cubic continuum center contains all three terms: a3(t)=H^2/(2d)+w'(t)H^3/(3w(t)d) +w''(t)H^4/(8w(t)d). Exact polynomial integration gives a3(t)=integral_(0..H) P3_t(t+u) du. In particular this center is not replaced by its leading term sqrt(t)/2. The private closed-form integration lemma is consumed in the centered-error proof.

For each prime q use the canonical firstClock tau_q, with q<tau_q<q+1. The source actualKernel includes its initial endpoint t<=tau_q. The proof consumes complete_original_first_clock_exclusion on S, which is disjoint from every closed interval [q,tau_q]. Therefore t is never tau_q on S, so t<=tau_q is equivalent to t<tau_q there. The same exclusion also implies q>t for an active clock tau_q>t. The clock bracket alone would not justify deleting the initial endpoint.

Define Phi_act(t) as the sum over all prime q<=floor(2R) of log(q)*actualKernel(lambda,t,t+H,w(t)d,tau_q), minus the exact integral_(0..H) k_t(t+u) du. Define Phi3(t) as sum_(t<tau_q<=t+H) log(q)P3_t(tau_q)-a3(t), using that same finite prime inventory. Since t<=R and H<=t on S, every contributing prime satisfies q<tau_q<=2R; the inventory omits no contributing prime.

The analytic premises remain explicit. For every t in S assume sum_(q prime, q<=floor(2R), t<tau_q<=t+H) log(q)<=3H, and assume that both Phi_act and Phi3 are IntegrableOn S. Under exactly these premises the conclusion is |integral_S Phi_act-integral_S Phi3| <=40 ell^(-1/10) M. No positive-mass premise is added; the statement also retains M=0. No component count or factor R/ell appears in the budget.

The derivative engine is reused from LogLogHigherDerivative.positiveKernel and its existing hasDerivAt_positiveKernel supplier. On t>1, w=K(1,0,0), w'=-K(2,0,0), w''=K(3,0,0), w'''=-K(4,0,0). Expanding this same recursion gives -w'''(t)=t^(-5)[24/log(t)+50/log(t)^2+70/log(t)^3 +60/log(t)^4+24/log(t)^5]. For t>=3, 0<=-w'''(s)<=228w(t)/t^3 for every s>=t, using the existing antitonicity of the original activation density.

Three derivative comparisons give a quadratic-density remainder bounded by [228w(t)/t^3]u^3/6. The fundamental theorem of calculus then gives 0<=P3_t(t+u)-k_t(t+u) <=228(H^4-u^4)/(24t^3d). Its uniform bound is (19/2)H^4/(t^3d), and its exact integrated bound is (38/5)H^5/(t^3d). The prime-mass premise bounds the weighted prime error by (57/2)H^5/(t^3d). Thus the two absolute errors sum to (361/10)H^5/(t^3d), which is at most 40H^5/(t^3d). The exact power identity H^5/(t^3d)=t^(-1/10), followed by integration over the same S, supplies the stated budget.

The GM mass premise is a Library input, not a compiled D5 Guth--Maynard theorem. Its provenance is the uniform Corollary 1.3 recorded in Library/Analytic/guthmaynard2024largevalues.md and the all-real common-start statement in Library/ArithSums/nicolas2025comparison.md; the underlying paper is arXiv:2405.20552v2. The admitted length range is y^(7/12)<=v<=y^(99/100). At one sufficiently late common start, H=t^(4/5) lies in that range and the relative counting and logarithmic-weight errors give the displayed 3H bound. On S the closed exclusion permits the original prime interval (t,t+H]. Without that exclusion, q<tau_q<q+1 only encloses active primes in (t-1,t+H], so GM must instead use y=t-1 and v=H+1. No numerical common start is asserted.

This is a repository derivation from the existing price, clock-exclusion and derivative suppliers and classical calculus. The existing A13 warning about a leading-baseline absolute error is retained as prior source, and no literature-priority claim is made for Taylor expansion. The theorem controls replacement error only. It supplies no favorable full signed lower bound for Phi3, no fixed kappa<sqrt(2)/4 for EL.14, no cofinal original witnesses, and no proof of RH or unrestricted Robin. The explicit GM and integrability premises are not discharged here.

## References

- Truth anchor: `D5/S3/Arith/Robin/ThirdOrderPrimeKernel.complete_selected_actual_prime_error`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/LogLogHigherDerivative](LogLogHigherDerivative.md)
- Dependency: [D5/S3/Arith/Robin/OriginalFirstClockTransport](OriginalFirstClockTransport.md)
