# Prime Structure of Actual Price Records

## Abstract

Same-integer prime structure, higher-layer confinement and qualitative localization for positive-price records.

Write X=log(m), L=log(X), lambda0=1/(40*X*L), and Q(m)=sum over prime factors p of Nat(v_p(m)-1)*log(p). The largest prime P is OriginalEndpointPrimeTail.largestPrime(m). A predecessor record at price lambda compares the literal goldenResourceObjective(lambda,n) with goldenResourceObjective(lambda,m) for every natural n with 0<n<m. In particular, one and two remain rivals.

**Theorem 1.1 (Finite prime-square tail from two-sided theta control).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.finite_theta_abel_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.finite_theta_abel_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real y,z,rho with 1<y, y<=z and 0<=rho, if (1-rho)*t<=theta(t)<= (1+rho)*t for every real t in [y,z], the sum of 1/p^2 over the prime filter of Finset.Ioc(floorNat(y),floorNat(z)) is at most (1+3*rho)/(y*log(y)). The lower cutoff is strict. Abel summation controls the log-weighted sum, and log(y)<=log(p) removes the weight. This is the original finite supplier also used by the actual-record Euler-tail bound.

**Theorem 1.2 (Antitone valuations and initial prime support at every positive price).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=2 and every lambda>0, the full strict predecessor record forces v_q(m)<=v_p(m) for all primes p<q, including zero valuations, and primeFactors(m)=primesLE(largestPrime(m)). The antitone companion must equal m because a smaller companion would improve the positive-price score even when its normalized divisor sum only ties. Nonempty support and its existing supremum then close every missing-prime position.

**Theorem 1.3 (Occupied layers embed into the canonical strict integer).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural m and every real lambda>0, a strict predecessor record at lambda implies m divides strictInteger(lambda). For an occupied prime p, the predecessor m/p is positive and smaller. The public single-layer objective difference makes its last marginal strictly larger than lambda. Exact strict-layer membership bounds the valuation by that of the same canonical integer. Zero valuations and nonprime coordinates contribute zero.

At any t>=2 with q_t=1/(t*log(t))<=lambda, canonical price divisibility gives m divides strictInteger(q_t). Only this full integer has the literal strictInteger_counts law. The full-inventory higher-layer estimate and active-power cutoff apply there; valuation and higher-mass monotonicity transfer them to m.

**Theorem 1.4 (An absolute square-root envelope for the same record integer).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one K>0 such that every m>=3 with the full predecessor record at lambda0 has nonincreasing valuations along all primes, including zero valuations; primeFactors(m)=primesLE(P); and X=theta(P)+Q(m). Moreover 0<=Q(m)<=2*theta(sqrt(80*X))+2*(psi(40*X)-theta(40*X))<=K*sqrt(X). Consequently X-K*sqrt(X)<=theta(P)<=X. The same m divides strictInteger(1/(40*X*log(40*X))), and every occupied positive layer k satisfies p^k<40*k*X.

The strongest antitone normal-form theorem supplies a companion a<=m with at least the same normalized divisor sum. If a<m, log monotonicity and the strictly positive price make its score strictly better, contradicting the record. Thus a=m. Nonempty prime support and its existing finite supremum then include every prime at most P. The original finite logarithmic factorization split identifies the first-prime mass with theta(P).

Take t=40*X. Since log(3)>1, its price is positive and strictly less than lambda0. Apply the complete higher-layer theorem to the full canonical inventory at this price, then use m dividing it to compare Q. If psi(t)-theta(t)<=c*sqrt(t), put C=abs(c). The bounds theta(y)<=log(4)*y and sqrt(2*t)<=2*sqrt(t) give K=sqrt(40)*(4*log(4)+2*C)>0. This argument imposes no full-count or global optimality condition on m, and does not identify m with its containing inventory.

**Theorem 1.5 (One log-size cutoff for each prime-localization tolerance).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon>0 there is A>0 such that all natural m>=3 with A<=log(m) and the same full record at lambda0 satisfy abs(P/log(m)-1)<epsilon. The cutoff precedes all such integers.

For X>=4*K^2 the finite mass envelope gives theta(P)>=X/2. Chebyshev's global upper bound then gives P>=X/(2*log(4)), so P passes any fixed qualitative PNT cutoff once X is large. Combine theta(P)/P tending to one with Q(m)/X bounded by K/sqrt(X) tending to zero, and use X=theta(P)+Q(m). Only Q(m)/X has the stated square-root rate; no such rate is claimed for the total P/X error.

These are log-size statements conditional on actual price records. Converting a uniform least-crossing height into the required record and log-size hypotheses is a separate arithmetic-analytic bridge. No crossing existence, unbounded crossing family, Robin sign or Riemann hypothesis follows from this dependency alone.

**Theorem 1.6 (A uniform sharp Euler-tail upper bound for the same record integer).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.actual_record_tail_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.actual_record_tail_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is A>0 such that, simultaneously for all alpha in [1/40,1] and all m>=3 with X=log(m)>=A, a strict record at lambda=alpha/(X*log(X)) implies sqrt(P)*log(P)*tail(m)<=2*sqrt(1-alpha/2)+epsilon. Here P is the original largestPrime(m), and tail and layerTail are exactly the original finite Euler truncation sums. Every positive predecessor, including one and two, occurs in the record premise.

Lowering lambda to lambda0 preserves the record: the score difference gains (lambda-lambda0)*(log(m)-log(n)). The existing largest-prime localization therefore applies uniformly in alpha. Put c=1-alpha/2, choose positive kappa and rho, and split at u=P^(1/3) and y=sqrt(P/(c+kappa)). The retained exchange price forces v_q(m)>=2 for every prime u<q<=y, including exclusion of both zero and one valuations. Indeed, if v_q<=1, its gain is at least (1-1/q)/q^2. Once 1/u<=kappa/4 and P*log(P/2)/(X*log(X))>=1-kappa/2, the gain multiplied by P is at least c+3*kappa/4 and the retained price is at least alpha/2-kappa/4. Their sum exceeds the exchange bound one.

Finite Abel summation with the coefficients log(q) at primes and zero elsewhere gives sum over y<q<=P of 1/q^2 at most (1+3*rho)/(y*log(y)), provided (1-rho)*t<=theta(t)<= (1+rho)*t throughout [y,P]. The boundary terms are theta(P)/P^2-theta(y)/y^2, and the integral is 2*integral(theta(t)/t^3). Qualitative PNT supplies this whole-interval condition after a fixed lower cutoff.

The small-prime contribution is at most 2*u/P=2/u^2. The middle contribution is at most sum(2/q^3)<=4/u^2, using the existing integer square-tail bound and q>u. The remaining actual factors contribute at most (1+3*rho)/((1-1/P)*y*log(y)). The prime q=P occurs only in this last band, where its actual valuation is at least one. Thus sqrt(P)*log(P)*tail(m) is at most 6*P^(-1/6)*log(P)+2*(1+3*rho)*sqrt(c+kappa)/(1-1/P).

Choose kappa=min(1/160,epsilon/32) and rho=min(1/4,epsilon/96) before alpha and m. A fixed P0 pays the PNT cutoff, 1/u, and the vanishing error 6*log(P)/P^(1/6)+4/(P-1). Localization with tolerance kappa/4 and X>=max(2*P0,exp(4*log(4)/kappa)) supplies the retained-price condition. The square-root difference is at most kappa since c>=1/2. These uniform choices pay the complete epsilon budget. No existence or unboundedness of records, global optimality, attainability of the constant, signed Mertens bound or RH is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.actual_record_tail_upper`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.finite_theta_abel_upper`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure`
- Dependency: [D5/S3/Arith/ExponentExchange/PrefixNormalForm](../ExponentExchange/PrefixNormalForm.md)
- Dependency: [D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer](../ExponentExchange/PriceRecordMissingLayer.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](OriginalEndpointPrimeTail.md)
