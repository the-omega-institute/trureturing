# Krizek's Phitorial Divisor-Sum Parity Characterization

## Abstract

The divisor sum of phitorials is odd exactly away from twice a square.

**Definition 1.1 (The product of totatives).**

$$\forall m \in \mathbb{N},\; \operatorname{phitorial}\left(m\right) = \prod_{k \in [1, m], \operatorname{Coprime}\left(k, m\right)} k$$

*Formalization.* `D5/S3/Arith/KrizekPhitorialDivisorSumParity.phitorial` (`✓ std3`).

*Citation.* Jaroslav Krizek (2017). *OEIS A280258, sum of phitorials over divisors*. URL: <https://oeis.org/A280258>.

*Commentary.*

The product ranges over all k in the inclusive interval from one to m that are coprime to m. For m=1 the value is one. For m at least two, the endpoint m is removed because gcd(m,m) is not one, so the inclusive and half-open readings agree there.

**Definition 1.2 (The sum of phitorials over divisors).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} \operatorname{phitorial}\left(d\right)$$

*Formalization.* `D5/S3/Arith/KrizekPhitorialDivisorSumParity.a` (`✓ std3`).

*Citation.* Jaroslav Krizek (2017). *OEIS A280258, sum of phitorials over divisors*. URL: <https://oeis.org/A280258>.

*Commentary.*

For each natural n, the value a(n) is the sum of phitorial(d) over the positive divisors d of n.

**Definition 1.3 (The printed parity claim).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; (n > 0) \Rightarrow ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right)) \Leftrightarrow (\neg (\exists k \in \mathbb{N},\; n = 2 \cdot {k}^{2})))\right)$$

*Formalization.* `D5/S3/Arith/KrizekPhitorialDivisorSumParity.claim` (`✓ std3`).

*Citation.* Jaroslav Krizek (2017). *OEIS A280258, sum of phitorials over divisors*. URL: <https://oeis.org/A280258>.

*Commentary.*

The domain is positive n. The single biconditional says that a(n) is odd precisely when n is not twice a square, combining the two parity classes printed in the source.

**Theorem 1.4 (The phitorial divisor-sum parity characterization).**

$$\forall n \in \mathbb{N},\; (n > 0) \Rightarrow ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right)) \Leftrightarrow (\neg (\exists k \in \mathbb{N},\; n = 2 \cdot {k}^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/KrizekPhitorialDivisorSumParity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2017). *OEIS A280258, sum of phitorials over divisors*. URL: <https://oeis.org/A280258>.

*Commentary.*

A phitorial is odd exactly at one and at even inputs. The number of divisors of a positive integer is odd exactly for a square, while halving the even divisors of 2m gives a bijection with the divisors of m. These facts determine the parity of the divisor sum.

## References

- Truth anchor: `D5/S3/Arith/KrizekPhitorialDivisorSumParity.a`
- Truth anchor: `D5/S3/Arith/KrizekPhitorialDivisorSumParity.claim`
- Truth anchor: `D5/S3/Arith/KrizekPhitorialDivisorSumParity.phitorial`
- Truth anchor: `D5/S3/Arith/KrizekPhitorialDivisorSumParity.result`
