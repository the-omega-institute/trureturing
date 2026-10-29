# Original endpoint prime tails

## Abstract

All-price prime tails for the original strict and maximal resource optimizers.

Both original endpoints, all positive prices, all primes and layers, and simultaneous ties are retained. The strict EndpointRobinEstimates sign and the original global Robin goal remain open.

**Lemma 1.1 (The existing pointwise endpoint tail estimates).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.endpoint_local`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.endpoint_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing endpoint_local declaration is made public with its statement and proof body unchanged for the weighted upper-scale consumer. For q>0, either original endpoint, a prime p and a_p>=1, its complete local tail is nonnegative, lies between the existing lowerPrice and upperPrice, and is at most both p/(p-1)*(exp(q log(p))-1) and 5/(4p^2). All original layer and tie conditions are retained. This visibility change reuses the original proof.

**Lemma 1.2 (Sharp local prices, the exact residual, and a uniform same-integer tail estimate).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.original_endpoint_prime_tail_supply`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.original_endpoint_prime_tail_supply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The r4463 source supplier is reused with attribution to its r4454 scalar sandwich. At either original endpoint the complete finite Euler tail lies between the sums of the sharp local prices L and U and is at most 7/(2*sqrt(u)), where u is this endpoint's own largest prime. The retained quantitative proof uses endpoint_small and the adaptive small/large support split, including the small-u and empty-support branches. The exact factorization keeps A=log(N). No lcm transfer, finite layer cap, arithmetic certificate or final-sign hypothesis is used. The first-layer refinement explained in the following paragraphs is paper mathematics; the cited Lean theorem supplies the sharp price bounds, nonnegative complete tail, square-root estimate and exact margin decomposition.

For each real q>0 and either original endpoint N, let S=N.primeFactors, a_p=N.factorization(p), m(p,k)=goldenLayerMarginal p k, u=largestPrime(N), A=log N, z_p=exp(q log p), t_p=-log(1-p^(-(a_p+1))), L_p=log((p z_p-1)/((p-1)z_p)) and T=sum_S t_p. All sums use this endpoint's complete support and all its layers. Let C be {p in S : m(p,2)<=q} at the strict endpoint and {p in S : m(p,2)<q} at the maximal endpoint; put H=S\C. Among primes in S, a_p>=1. The exact k=2 classifier makes p in C equivalent to not(2<=a_p), hence to a_p=1, with the stated strict/weak tie conventions. Thus H consists exactly of the support primes with a_p>=2.

Set c_p=-log(1-p^-2), B=sum_C c_p+sum_H L_p and J=sum_H(t_p-L_p). On C, t_p=c_p exactly and the retained local sandwich gives L_p<=c_p. On H, the retained local sandwich gives t_p-L_p>=0. Consequently sum_S L_p<=B, J>=0 and T=B+J, by adding c_p+0=t_p on C and L_p+(t_p-L_p)=t_p on H. In particular B<=T and margin(N)=E3(u)+B+log(log A)-log(log u)+J. No higher-layer term has been discarded.

For any active strict-endpoint prime with a_p=1, strict selection gives q<m(p,1), hence 1<z_p<1+1/p. Here p>=2 and z_p>1, so 1-p^-2 and all displayed denominators are positive. Logarithmic algebra gives

c_p-L_p = log(p^2 z_p / ((p+1)(p z_p-1))) > 0,

because p^2 z_p-(p+1)(p z_p-1)=p+1-p z_p>0. To produce the original above-5040 family, first choose any prime p>5040, then set q_p=m(p,2) and N_p=strictInteger(q_p). Existing marginal positivity and layer strict decrease give q_p>0 and q_p<m(p,1). The k=1 classifier selects p and the k=2 classifier excludes its second layer, so a_p=1 and p divides N_p. The original strictInteger_pos also gives N_p>0; hence N_p>=p>5040. This p supplies a strictly positive summand in B-sum_S L_p, while every other summand is nonnegative. Infinitely many primes p>5040 give this family of pairs (q_p,p); no claim of infinite support at a fixed q is made. At a maximal first-layer tie, z_p=1+1/p and the displayed difference is zero, so this strict-gain assertion is not transferred to every maximal tie.

The existing same-integer prime-prefix identity gives log(1-1/p)+c_p=-log(1+1/p) on C and log(1-1/p)+L_p=log(1-1/(p z_p)) on H. The prime-local logarithm arguments are positive. On the original Robin domain N>5040, A>1 and u>=2 also give the usual analytic domains for the iterated logarithms; outside that domain the original total Lean logarithm conventions remain. The support-prefix identity is E3(u)=gamma+log(log u)+sum_S log(1-1/p), so substituting T=B+J and cancelling log(log u) gives

(5) margin(N) = gamma + log(log A) - sum_C log(1+1/p) + sum_H log(1-1/(p z_p)) + J, (6) log(sigma(N)/N) <= sum_C log(1+1/p) - sum_H log(1-1/(p z_p)).

Indeed the exact Euler identity gives log(sigma(N)/N)=sum_C log(1+1/p)-sum_H log(1-1/(p z_p))-J; dropping only the nonpositive term -J proves (6). Thus (5) is an identity and (6) is its abundancy bound.

A second exact application uses a finite theta clock. For the same q>0 and either original endpoint, let u=largestPrime(N)>=4, A=log(N), s=theta(u), and let X>=u be any real number. The complete original prime prefix and logarithm factorization give A=s+D, where D=sum_S (a_p-1)log(p)>=0. Here natural subtraction is legitimate because every support exponent is at least one. Since the prefix contains prime 3, s>=log(3)>1, hence A>1; the displayed logarithms require no extra inventory or size assumption.

Put density(v)=(log(v)+1)/(v^2*log(v)^2) and J_X=integral from u to X of (theta(v)-v)*density(v). Generic finite Abel summation applied to the prime-log coefficients and the existing clock g(v)=1/(v log(v)) gives, for all real 2<=u<=X, J_X=E2p(X)-E2p(u)-(theta(X)-X)/(X log(X))+(theta(u)-u)/(u log(u)). The lower prime prefix is inclusive, so the prime difference contains exactly u<p<=X, including the prime-2 boundary. Integrating the elementary main term uses the primitive log(log(v))-1/log(v).

The existing Mertens E2p bound and Chebyshev estimate theta(X)<=log(4)*X give |J_X-((s-u)/(u log(u))-E2p(u))|<=C/log(X), where C=log(4)+7+E1. This also gives a genuine improper limit of the truncated interval integrals; it does not assert absolute Lebesgue integrability on an unbounded interval. For any s,u>1, the two ordinary logarithm defects at s/u and log(s)/log(u) give 0<=Q<=B, with Q=log(log(u))+(s-u)/(u log(u))-log(log(s)) and B=(s-u)^2/(s*u*log(u))+(log(s)-log(u))^2/(log(s)*log(u)). These are direct applications and algebraic consequences of existing results, rather than additional canonical theorem bindings.

Combining the exact original margin decomposition, E3(u)>=-E2p(u), the preceding cancellation and the existing tangent inequality yields J_X+T+D/(A log(A))-C/log(X)-B<=robinLogMargin(N). The theta endpoint discrepancy enters through the quadratic penalty B; the actual higher-layer inventory remains a favorable gain, and T is still the same integer's complete Euler tail. The complete finite-window statement was checked as a transient Lean calculation with only the standard classical axioms. This does not prove that its lower bound is positive, does not control the remaining theta or psi oscillation, and does not resolve RH. No new named Lean declaration is retained solely for these applications.

These are the original lower-control and equivalent prime-log derivations, not new canonical theorem bindings. Their exact original statements and Lean proof bodies remain transient. The remaining original obligation is strict positivity of E3(u)+T+log(log A)-log(log u) at both endpoints for every q>0 with strictInteger(q)>5040. J>=0 or a local strict gain does not prove that sign. Positivity of E3(u)+B+log(log A)-log(log u) would be sufficient, but is neither necessary nor proved here. The sharp upper-tail estimate cannot supply a lower sign.

**Theorem 1.3 (Finite same-integer min-cost correction and Robin decomposition).**

Lean statement: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.finite_min_tail_robin_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.finite_min_tail_robin_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural m, put X=log(m) and P=largestPrime(m). Under the explicit support equality m.primeFactors=Nat.primesLE(P) and the real domain condition 1<theta(P), the theorem sums, over every active prime including exponent-one primes, the minimum of log(p)/(X*log(X)) and -log(1-p^-2). It bounds this finite cost by the complete same-integer Euler tail plus the exact log-log clock difference log(log(X))-log(log(theta(P))).

The proof uses the canonical logarithm factorization log(m)=theta(P)+Q, where Q is the full sum of (factorization(p)-1)*log(p) with natural truncated subtraction on the actual support. The existing strict log-log tangent at X reverses to Q/(X*log(X))<=the clock difference. For valuation one the minimum is charged exactly to layerTail; for valuation at least two the first minimum argument is charged to its positive Q-term and layerTail is nonnegative. No exponent, prime, product, or optimizer endpoint is replaced by a cutoff.

The same declaration then consumes the canonical Mertens.E3 prefix identity and the shared general log-sigma/Euler helper to obtain V+E3(P)+log(log(theta(P)))-log(log(P))<=robinLogMargin(m). The support and theta hypotheses are finite theorem premises only; they do not assert actual-record structure, 5040 divisibility, RH, or the unresolved analytic 2*sqrt(2)-epsilon continuation.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.endpoint_local`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.finite_min_tail_robin_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalEndpointPrimeTail.original_endpoint_prime_tail_supply`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
- Dependency: [D5/S3/Arith/Robin/ActualGlobalBracketing](ActualGlobalBracketing.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerInventoryGrowth](EulerLayerInventoryGrowth.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](LogarithmBounds.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](../../Weil/GronwallLowerEnvelope.md)
