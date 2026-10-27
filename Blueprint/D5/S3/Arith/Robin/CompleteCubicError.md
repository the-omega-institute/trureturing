# An Elementary Complete-Domain Cubic Replacement Budget

## Abstract

Elementary cubic replacement error on the unchanged complete original selected domain, with ordinary integrability supplied and no prime-distribution premise.

Elementary active-prime counting and automatic response integrability give a vanishing replacement-error budget on the complete unchanged original domain, with no prime-distribution premise.

**Theorem 1.1 (Elementary active-prime counting yields a vanishing error per selected volume).**

Lean statement: `D5/S3/Arith/Robin/CompleteCubicError.complete_selected_cubic_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/CompleteCubicError.complete_selected_cubic_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take OriginalFirstClockTransport.OriginalWindow X, real ell and R, ell>=243, and OriginalBounds X ell R. Put S=selectedDomain X and M=volume.real S. These are all the hypotheses. There is no GM mass estimate, other prime-distribution premise, assumed response integrability or signed-response hypothesis. M=0 is retained.

For H(t)=windowLength t=t^(4/5) and d(t)=normalization t=t^(11/10), use the existing Phi_act(t)=canonicalActualPrimeResponse R t H(t) d(t) and Phi3(t)=cubicPrimeResponse R t H(t) d(t). The proposed conclusion is exactly |integral_S Phi_act(t) dt-integral_S Phi3(t) dt| <=408 ell^(-1/20) M. This is a bound on the difference of the literal centered responses, and the cubic center retains all three terms, not only its leading term.

S is the complete union of original good consecutive-label closed edges, with overlaps counted once. The original window, least full-domain maximizing sources over positive multiples of 5040p, strict inventories and actual first clocks remain unchanged. No favorable subfamily, edge trimming or new source selection is introduced.

The first new estimate genuinely uses the existing complete first-clock exclusion. For t in S and a prime q active under t<firstClock q<=t+H, the reused selected_firstClock_initial exclusion implies t<q. The existing clock bracket q<firstClock q then gives q<=t+H. Thus the active prime set is contained in the integer interval Ioc floor(t) floor(t+H). The clock bracket alone does not justify the lower endpoint t<q.

Counting every integer in that interval gives card(active primes)<=floor(t+H)-floor(t)<=H+1. Since t>=243 gives H>=1 and H<=t, this is at most 2H and every active q is at most 2t. Monotonicity of the logarithm therefore gives the elementary logarithmic mass bound sum_active log(q)<=2H log(2t). This argument uses no sieve theorem or asymptotic prime distribution.

The proof reuses ThirdOrderPrimeKernel's derivative and Taylor-remainder engine, its uniform kernel error (19/2)H^4/(t^3 d), its exact continuum error (38/5)H^5/(t^3 d), its complete cubic-center identity, and its equality between the literal actual response and the active-clock response on S. The elementary mass bound pays the weighted prime error by 19 log(2t) H^5/(t^3 d). Consequently the pointwise replacement error is at most [19 log(2t)+38/5] H^5/(t^3 d).

The existing scale identity H^5/(t^3 d)=t^(-1/10) is used exactly. The elementary logarithm inequality log(t)<=20 t^(1/20), together with log(2)<=1 and t^(1/20)>=1, gives log(2t)<=21 t^(1/20). Hence the pointwise error is at most (399+38/5)t^(-1/20)<=408t^(-1/20). Since ell<=t on S, the negative power is at most ell^(-1/20).

The proof directly consumes AutomaticCubicResponseIntegrability.complete_selected_responses_integrable to establish both ordinary IntegrableOn premises from the same OriginalBounds. Compactness of S supplies finite Lebesgue measure. The norm-of-integral inequality then integrates the uniform pointwise error over all of S, without a component-count factor or a factor R/ell.

This elementary alternative has a slower decay exponent than the existing 40 ell^(-1/10) estimate with its explicit 3H mass premise; it does not alter that theorem. The new steps are active-integer counting, logarithmic mass control and absorption of the logarithmic loss, combined with the separate integrability supplier. The calculus remainder and the original-domain transport are reused. No novelty priority is asserted for the classical estimates.

The factor 408 ell^(-1/20) tends to zero as ell grows, so the statement controls replacement error per unit selected volume; it does not assert that the total error tends to zero when M also varies. It does not supply a favorable full signed main term for Phi3, a fixed kappa<sqrt(2)/4 for EL.14, cofinal original witnesses, RH or unrestricted Robin. Those mathematical obligations remain beyond this replacement estimate. The signed prime-moment obligation remains open.

## References

- Truth anchor: `D5/S3/Arith/Robin/CompleteCubicError.complete_selected_cubic_error`
- Dependency: [D5/S3/Arith/Robin/AutomaticCubicResponseIntegrability](AutomaticCubicResponseIntegrability.md)
- Dependency: [D5/S3/Arith/Robin/OriginalFirstClockTransport](OriginalFirstClockTransport.md)
- Dependency: [D5/S3/Arith/Robin/ThirdOrderPrimeKernel](ThirdOrderPrimeKernel.md)
