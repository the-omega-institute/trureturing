# Krizek's Totative-Sum Divisor-Product Parity Conjecture

## Abstract

For every positive natural n, the product over the divisors of n of their totative sums is odd exactly when the totative sum of n is odd.

All variables and values lie in the natural numbers. The range ending at n+1 contains 0 through n, and filtering by Coprime(n,k) leaves the totatives of n. The notation mod(p,4) below is natural-number remainder. The set divisors(0) is empty, while divisors(n) for positive n is the finite set of positive divisors.

**Definition 1.1 (The sum of the totatives).**

$$\forall n \in \mathbb{N},\; \operatorname{totativeSum}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right), \operatorname{Coprime}\left(n, k\right)} k$$

*Formalization.* `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.totativeSum` (`✓ std3`).

*Citation.* Jaroslav Krizek (2016). *OEIS A280246, product of totative sums over divisors*. URL: <https://oeis.org/A280246>.

*Commentary.*

The summand k ranges over exactly the values from zero through n that are coprime to n. The endpoints contribute correctly: zero is retained only at n=1, while n itself is retained only at n=1.

**Definition 1.2 (The divisor product).**

$$\forall n \in \mathbb{N},\; \operatorname{divisorTotativeProduct}\left(n\right) = \prod_{d \in \operatorname{divisors}\left(n\right)} \operatorname{totativeSum}\left(d\right)$$

*Formalization.* `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.divisorTotativeProduct` (`✓ std3`).

*Citation.* Jaroslav Krizek (2016). *OEIS A280246, product of totative sums over divisors*. URL: <https://oeis.org/A280246>.

*Commentary.*

For each positive divisor d of n, the product contains one factor equal to the totative sum of d.

**Theorem 1.3 (The odd totative-sum classification).**

$$\forall n \in \mathbb{N},\; (\operatorname{Odd}\left(\operatorname{totativeSum}\left(n\right)\right)) \Leftrightarrow ((n = 1) \lor \left((n = 2) \lor (\exists p \in \mathbb{N}, k \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \land \left((p \bmod 4 = 3) \land \left((1 \le k) \land (n = p^{k})\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.odd_totativeSum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totative sums at one and two are odd. Above them, oddness forces a single odd prime factor, and the pairing of each reduced residue k with n-k (twice the totative sum equals n times the Euler totient) excludes primes congruent to one modulo four. Conversely, every positive power of a prime congruent to three modulo four has an odd totative sum.

**Theorem 1.4 (The divisor-product parity equivalence).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((\operatorname{Odd}\left(\operatorname{divisorTotativeProduct}\left(n\right)\right)) \Leftrightarrow (\operatorname{Odd}\left(\operatorname{totativeSum}\left(n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result` (`✓ std3`). ∎

*Citation.* Jaroslav Krizek (2016). *OEIS A280246, product of totative sums over divisors*. URL: <https://oeis.org/A280246>.

*Commentary.*

A finite natural product is odd exactly when each factor is odd. The odd totative-sum classification is closed under taking positive divisors, so oddness at n propagates to every divisor; the factor indexed by n gives the reverse implication.

## References

- Truth anchor: `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.divisorTotativeProduct`
- Truth anchor: `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.odd_totativeSum_iff`
- Truth anchor: `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result`
- Truth anchor: `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.totativeSum`
