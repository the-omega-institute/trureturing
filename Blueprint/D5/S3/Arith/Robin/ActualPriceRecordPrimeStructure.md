# Prime Structure of Actual Price Records

## Abstract

Same-integer prime structure, higher-layer confinement and qualitative localization for positive-price records.

Write X=log(m), L=log(X), lambda0=1/(40*X*L), and Q(m)=sum over prime factors p of Nat(v_p(m)-1)*log(p). The largest prime P is OriginalEndpointPrimeTail.largestPrime(m). A predecessor record at price lambda compares the literal goldenResourceObjective(lambda,n) with goldenResourceObjective(lambda,m) for every natural n with 0<n<m. In particular, one and two remain rivals.

**Theorem 1.1 (Antitone valuations and initial prime support at every positive price).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=2 and every lambda>0, the full strict predecessor record forces v_q(m)<=v_p(m) for all primes p<q, including zero valuations, and primeFactors(m)=primesLE(largestPrime(m)). The antitone companion must equal m because a smaller companion would improve the positive-price score even when its normalized divisor sum only ties. Nonempty support and its existing supremum then close every missing-prime position.

**Theorem 1.2 (Occupied layers embed into the canonical strict integer).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural m and every real lambda>0, a strict predecessor record at lambda implies m divides strictInteger(lambda). For an occupied prime p, the predecessor m/p is positive and smaller. The public single-layer objective difference makes its last marginal strictly larger than lambda. Exact strict-layer membership bounds the valuation by that of the same canonical integer. Zero valuations and nonprime coordinates contribute zero.

At any t>=2 with q_t=1/(t*log(t))<=lambda, canonical price divisibility gives m divides strictInteger(q_t). Only this full integer has the literal strictInteger_counts law. The full-inventory higher-layer estimate and active-power cutoff apply there; valuation and higher-mass monotonicity transfer them to m.

**Theorem 1.3 (An absolute square-root envelope for the same record integer).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one K>0 such that every m>=3 with the full predecessor record at lambda0 has nonincreasing valuations along all primes, including zero valuations; primeFactors(m)=primesLE(P); and X=theta(P)+Q(m). Moreover 0<=Q(m)<=2*theta(sqrt(80*X))+2*(psi(40*X)-theta(40*X))<=K*sqrt(X). Consequently X-K*sqrt(X)<=theta(P)<=X. The same m divides strictInteger(1/(40*X*log(40*X))), and every occupied positive layer k satisfies p^k<40*k*X.

The strongest antitone normal-form theorem supplies a companion a<=m with at least the same normalized divisor sum. If a<m, log monotonicity and the strictly positive price make its score strictly better, contradicting the record. Thus a=m. Nonempty prime support and its existing finite supremum then include every prime at most P. The original finite logarithmic factorization split identifies the first-prime mass with theta(P).

Take t=40*X. Since log(3)>1, its price is positive and strictly less than lambda0. Apply the complete higher-layer theorem to the full canonical inventory at this price, then use m dividing it to compare Q. If psi(t)-theta(t)<=c*sqrt(t), put C=abs(c). The bounds theta(y)<=log(4)*y and sqrt(2*t)<=2*sqrt(t) give K=sqrt(40)*(4*log(4)+2*C)>0. This argument imposes no full-count or global optimality condition on m, and does not identify m with its containing inventory.

**Theorem 1.4 (One log-size cutoff for each prime-localization tolerance).**

Lean statement: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon>0 there is A>0 such that all natural m>=3 with A<=log(m) and the same full record at lambda0 satisfy abs(P/log(m)-1)<epsilon. The cutoff precedes all such integers.

For X>=4*K^2 the finite mass envelope gives theta(P)>=X/2. Chebyshev's global upper bound then gives P>=X/(2*log(4)), so P passes any fixed qualitative PNT cutoff once X is large. Combine theta(P)/P tending to one with Q(m)/X bounded by K/sqrt(X) tending to zero, and use X=theta(P)+Q(m). Only Q(m)/X has the stated square-root rate; no such rate is claimed for the total P/X error.

These are log-size statements conditional on actual price records. Converting a uniform least-crossing height into the required record and log-size hypotheses is a separate arithmetic-analytic bridge. No crossing existence, unbounded crossing family, Robin sign or Riemann hypothesis follows from this dependency alone.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_divides_strictInteger`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_largest_prime_localization`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_confinement`
- Truth anchor: `D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.price_record_prime_structure`
- Dependency: [D5/S3/Arith/ExponentExchange/PrefixNormalForm](../ExponentExchange/PrefixNormalForm.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](OriginalEndpointPrimeTail.md)
