# Hanna's A301432 divisibility conjecture

## Abstract

Hanna's A301432 coefficients are integer multiples of 21 at every positive index.

**Definition 1.1 (The source coefficient series).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum'_{k: \mathbb{N}} \frac{(3: \mathbb{R})^{k} \cdot (\operatorname{Nat.choose}(k^{2}) n: \mathbb{R})}{(4: \mathbb{R})^{k + 1}}$$

*Formalization.* `D5/S3/ArithSums/HannaA301432Divisibility.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

OEIS A301432, FORMULA line 3 (unpaginated): a(n) = Sum_{k>=0} 3^k * binomial(k^2, n) / 4^(k+1). Here n and k range over natural numbers, Nat.choose is the ordinary natural binomial coefficient, and the infinite sum is taken in the real numbers.

**Definition 1.2 (The published positive-index assertion).**

$$claim = \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (21: \mathbb{R}) \cdot (q: \mathbb{R})\right)\right)$$

*Formalization.* `D5/S3/ArithSums/HannaA301432Divisibility.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

OEIS A301432, COMMENTS line 1 (unpaginated): a(n) is divisible by 21 for n>0 (conjecture). The positive integer index is encoded by 1 <= n, and divisibility is encoded by the existence of an integer q whose real multiple by 21 equals a(n).

**Theorem 1.3 (The divisibility theorem).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (21: \mathbb{R}) \cdot (q: \mathbb{R})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301432Divisibility.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

The convergent geometric average at m=3 is m(2m+1) times an integer, giving the factor 21. Summability is proved before identifying the infinite sum.

## References

- Truth anchor: `D5/S3/ArithSums/HannaA301432Divisibility.a`
- Truth anchor: `D5/S3/ArithSums/HannaA301432Divisibility.claim`
- Truth anchor: `D5/S3/ArithSums/HannaA301432Divisibility.result`
- Dependency: [D5/S3/ArithSums/HannaA301310Divisibility](HannaA301310Divisibility.md)
