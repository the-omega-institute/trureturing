# Edge Propagation of Robin's Inequality Along Prime Fibres

## Abstract

A multiplicative edge test carries Robin's inequality, its first layer controls a whole prime fibre, and prime replacement keeps it.

Write Z(n)=sigma(n)/n and RobinAt(n) for Z(n)<exp(gamma)*log(log(n)). For a step n -> n*m the edge test EdgeTest(n,m) asks that (Z(n*m)/Z(n)-1)*log(log(n)) <= log(1+log(m)/log(n)). Since log(log(n*m))=log(log(n))+log(1+log(m)/log(n)), the test says that the relative increase of Z, weighted by log(log(n)), is paid by the increase of the double logarithm. It discards the existing Robin slack at n, so it is sufficient for propagation and not necessary.

**Theorem 1.1 (Positivity of the normalized divisor sum).**

Lean statement: `D5/S3/Arith/Robin/PrimeFiberPropagation.divisorRatio_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeFiberPropagation.divisorRatio_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n with n!=0, divisorRatio(n)>0. The numerator sigma(1,n) and the denominator n are both positive. This permits logarithmic product identities at arbitrary positive arithmetic corners; no coprimality condition is needed for positivity.

**Theorem 1.2 (A passing edge carries Robin's inequality).**

Lean statement: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_of_edgeTest`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_of_edgeTest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For naturals n>1 and m>0, RobinAt(n) and EdgeTest(n,m) imply RobinAt(n*m). The multiplier m is arbitrary; m=q^r gives the step along one prime direction. With rho=Z(n*m)/Z(n)>0 the test gives rho*log(log(n)) <= log(log(n*m)). Robin at n forces log(log(n))>0, and multiplying the strict inequality by rho gives Z(n*m)=rho*Z(n)<exp(gamma)*log(log(n*m)).

No estimate on sigma beyond its positivity is used. The statement does not decide whether a given edge passes; that is a separate numerical or analytic question.

**Theorem 1.3 (The first layer of a prime fibre controls every later layer).**

Lean statement: `D5/S3/Arith/Robin/PrimeFiberPropagation.edgeTest_mul_prime_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeFiberPropagation.edgeTest_mul_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be prime and let n satisfy log(n)>=3. If EdgeTest(n,q) holds, then EdgeTest(n*q^k,q) holds for every k. The excess of one more factor q is exactly Z(n*q)/Z(n)-1=1/(q*sigma(q^a)) with a the exponent of q in n, from sigma multiplicativity and sigma(q^(a+1))=q*sigma(q^a)+1. The next excess is therefore at most the present one divided by q.

Put L=log(n) and l=log(q). The step uses log(1+l/L)<=l/L, log(L+l)<=log(L)+l/L, log(1+l/(L+l))>=l/(L+2l), log(L)>=1, and (L+l)(L+2l)<=L^2*(1+l+l^2/2)<=L^2*exp(l), the middle inequality using L>=3. Together they turn the test at scale L into the test at scale L+l. No restriction q>7 is needed; every prime direction behaves the same way.

**Theorem 1.4 (Robin's inequality along a whole prime fibre).**

Lean statement: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_prime_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If q is prime, log(n)>=3, RobinAt(n) holds and EdgeTest(n,q) passes, then RobinAt(n*q^k) holds for all k. Induction combines the two theorems above; log(n*q^k)>=log(n)>=3 keeps every layer in the domain of the fibre step.

Combined with the frozen seven-smooth theorem, every certified seven-smooth core B>5040 whose first q-layer passes the test certifies the whole fibre B*q^k. The test can fail where Robin still holds: for B=27440=2^4*5*7^3 and q=11 the first layer fails numerically, while 301840=27440*11 satisfies Robin with margin. Most integers have seven-smooth part at most 5040 and are not reached from that core at all. The theorem therefore reduces each prime fibre to its first layer; it does not prove Robin's inequality for all n>5040, and the Riemann hypothesis remains open.

**Theorem 1.5 (Replacing a prime by a larger prime keeps Robin's inequality).**

Lean statement: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_prime_replace`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_prime_replace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p<=q be primes, neither dividing m, and a any exponent. If RobinAt(p^a*m) holds, then Z(q^a*m)<exp(gamma)*log(log(q^a*m)). The normalized divisor-sum factorization of ExponentExchange.IntegerSwap gives Z(r^a*m)=G_r(a)*Z(m) with G_r(a) the sum of r^(-i) for i<=a. Each term of G_q(a) is at most the matching term of G_p(a), so the divisor ratio does not increase, while q^a*m>=p^a*m makes the double logarithm no smaller.

Repeating the replacement from the largest prime down moves a certified exponent pattern 2^a1*3^a2*5^a3*... to every integer q1^a1*q2^a2*q3^a3*... with distinct primes q1<q2<q3<... . Starting from the seven-smooth and eleven-smooth theorems, every integer above 5040 with at most five distinct primes whose compression to the first primes exceeds 5040 is certified this way. A compression at most 5040 needs a separate argument, and integers with six or more distinct primes are not reached.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimeFiberPropagation.divisorRatio_pos`
- Truth anchor: `D5/S3/Arith/Robin/PrimeFiberPropagation.edgeTest_mul_prime_pow`
- Truth anchor: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_of_edgeTest`
- Truth anchor: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_mul_prime_pow`
- Truth anchor: `D5/S3/Arith/Robin/PrimeFiberPropagation.robinAt_prime_replace`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](../ExponentExchange/IntegerSwap.md)
