# Robin's Inequality for Integers with at Most Eight Distinct Primes

## Abstract

Robin's inequality holds above 5040 for every integer with at most eight distinct prime factors, hence for every integer between 5040 and 223092870.

**Theorem 1.1 (At most eight distinct prime factors).**

Lean statement: `D5/S3/Arith/Robin/FewDistinctPrimes.robin_of_card_primeFactors_le_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FewDistinctPrimes.robin_of_card_primeFactors_le_eight` (`✓ std3`). ∎

*Citation.* Emmanuel Elima (2022). *On Robin's inequality for positive integers and related bounds*. URL: <https://easychair.org/publications/preprint/xW8q>.

*Commentary.*

For every natural number n > 5040 whose set of prime factors has at most eight elements, sigma(1,n)/n < e^gamma*log(log(n)). Exponents are unrestricted and no Riemann Hypothesis premise is used.

For n >= 6000 the frozen normal-form theorem gives m <= n with as many distinct primes, non-increasing exponents and sigma(1,n)/n <= sigma(1,m)/m. If m <= 5040, the frozen optimum of sigma(1,m)/m - m^(1/25) at 5040 gives sigma(1,m)/m <= 403/105, while e^gamma > 89/50 and log(log(6000)) > 54/25 give a capacity above 3.84. If m > 5040, at most eight distinct primes and decreasing exponents force m = 2^a*3^b*5^c*7^d*11^e*13^f*17^g*19^h with a >= b >= ... >= h.

Below 10^12 a kernel-checked recursive enumeration visits all 4271 such products, carrying their divisor sums, and certifies 100*sigma(1,m) <= K*m on twelve intervals starting at 5040, 10080, 25200, 55440, 110880, 332640, 1441440, 7207200, 61261200, 367567200, 3491888400 and 41902660800, with K = 381, 395, 411, 425, 436, 452, 471, 490, 513, 530, 549, 568. A rational lower bound for log(log(t)) at each left end t, derived from the frozen dyadic logarithm brackets, pays each K/100. From 10^12 on, the product of p/(p-1) over the first eight primes, 323323/55296 < 5.85, is below 89/50*3317/1000 < e^gamma*log(log(10^12)). Robin's inequality at m then passes to n because n >= m.

For 5040 < n < 6000 the normal form could be 5040 itself, so this range is treated directly: an 11-smooth n is covered by the frozen eleven-smooth theorem, and otherwise a prime p >= 13 divides n, the factor sigma(1,p^a)/p^a is at most 13/12, the cofactor is below 462, and a kernel check gives sigma(1,r)/r <= 13/4 for r < 462.

Elima states the bound for at most twelve distinct primes by reduction to 21-full integers and calculation, and `D5/L/ArithSums/mishra2026finiterobin` states a stronger omega-graded bound for at most six distinct primes; neither is a machine verification, and this proof uses neither. Integers with nine or more distinct prime factors are not covered, and the Riemann hypothesis remains open.

**Theorem 1.2 (Every integer between 5040 and the ninth primorial).**

Lean statement: `D5/S3/Arith/Robin/FewDistinctPrimes.robin_lt_223092870`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FewDistinctPrimes.robin_lt_223092870` (`✓ std3`). ∎

*Citation.* Alexander Hertlein (2018). *Robin's inequality for new families of integers*. URL: <https://arxiv.org/pdf/1612.05186v2>.

*Commentary.*

For every natural number n with 5040 < n < 223092870, where 223092870 = 2*3*5*7*11*13*17*19*23, sigma(1,n)/n < e^gamma*log(log(n)).

Nine distinct primes have product at least 223092870: removing the largest prime of a set of k <= 9 primes leaves k-1 primes, and the largest one is at least the k-th prime because fewer than k primes lie below it. So every n in the range has at most eight distinct prime factors and the theorem above applies.

The finite range is far inside the computationally verified range 5040 < n <= 10^(10^10) recorded by Hertlein; the point here is a kernel certificate independent of that computation.

## References

- Truth anchor: `D5/S3/Arith/Robin/FewDistinctPrimes.robin_lt_223092870`
- Truth anchor: `D5/S3/Arith/Robin/FewDistinctPrimes.robin_of_card_primeFactors_le_eight`
- Dependency: [D5/S3/Arith/ExponentExchange/PrefixNormalForm](../ExponentExchange/PrefixNormalForm.md)
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../GoldenResourceOptimalInteger.md)
- Dependency: [D5/S3/Arith/Robin/ElevenSmooth](ElevenSmooth.md)
