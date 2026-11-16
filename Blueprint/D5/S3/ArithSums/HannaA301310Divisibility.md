# Hanna's A301310 divisibility conjecture

## Abstract

Hanna's A301310 coefficients are integer multiples of 10 at every positive index.

**Theorem 1.1 (Evaluation of iterated polynomial differences).**

$$\forall P \in \mathbb{Q}[X],\; \forall j \in \mathbb{N},\; \forall x \in \mathbb{Q},\; \operatorname{Polynomial.eval}\left(x, \operatorname{Function.iterate}\left((fun (Q: \mathbb{Q}[X]) \mapsto \operatorname{fwdDiff}\left((1: \mathbb{Q}[X]), (fun (U: \mathbb{Q}[X]) \mapsto \operatorname{Polynomial.comp}\left(Q, U\right)), X\right)), j, P\right)\right) = \operatorname{Function.iterate}\left(\operatorname{fwdDiff}\left((1: \mathbb{Q})\right), j, (fun (y: \mathbb{Q}) \mapsto \operatorname{Polynomial.eval}\left(y, P\right))\right)\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301310Divisibility.eval_diff_iter_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

Evaluating the jth forward difference of a rational polynomial at x equals the jth forward difference of its evaluation function at x. The polynomial step is composition with X+1 minus composition with X. This identity relates polynomial degree bounds to differences of values.

**Theorem 1.2 (Integer values and rational polynomial differences).**

$$\forall P \in \mathbb{Q}[X],\; \forall f \in \mathbb{N} \to \mathbb{Z},\; (\forall k \in \mathbb{N},\; \operatorname{Polynomial.eval}\left((k: \mathbb{Q}), P\right) = (f\left(k\right): \mathbb{Q})) \Rightarrow \left(\forall j \in \mathbb{N},\; (\operatorname{Function.iterate}\left(\operatorname{fwdDiff}\left((1: \mathbb{N})\right), j, f\right)\left(0\right): \mathbb{Q}) = \operatorname{Polynomial.eval}\left(0, \operatorname{Function.iterate}\left((fun (Q: \mathbb{Q}[X]) \mapsto \operatorname{fwdDiff}\left((1: \mathbb{Q}[X]), (fun (U: \mathbb{Q}[X]) \mapsto \operatorname{Polynomial.comp}\left(Q, U\right)), X\right)), j, P\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301310Divisibility.coeff_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

If a rational polynomial agrees with an integer sequence at every natural input, casting the sequence's jth forward difference at zero to the rationals gives the evaluation at zero of the polynomial's jth forward difference. The value correspondence is assumed for every natural index.

**Definition 1.3 (The source coefficient series).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum'_{k: \mathbb{N}} \frac{(2: \mathbb{R})^{k} \cdot (\operatorname{Nat.choose}(k^{2}) n: \mathbb{R})}{(3: \mathbb{R})^{k + 1}}$$

*Formalization.* `D5/S3/ArithSums/HannaA301310Divisibility.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

OEIS A301310, FORMULA line 3 (unpaginated): a(n) = Sum_{k>=0} 2^k * binomial(k^2, n) / 3^(k+1). Here n and k range over natural numbers, Nat.choose is the ordinary natural binomial coefficient, and the infinite sum is taken in the real numbers.

**Definition 1.4 (The published positive-index assertion).**

$$claim = \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (10: \mathbb{R}) \cdot (q: \mathbb{R})\right)\right)$$

*Formalization.* `D5/S3/ArithSums/HannaA301310Divisibility.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

OEIS A301310, COMMENTS line 2 (unpaginated): a(n) is divisible by 10 for n>0 (conjecture). The positive integer index is encoded by 1 <= n, and divisibility is encoded by the existence of an integer q whose real multiple by 10 equals a(n).

**Theorem 1.5 (Square-binomial geometric averages).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall m \in \mathbb{N},\; \exists q \in \mathbb{Z},\; \operatorname{HasSum}\left((fun (k: \mathbb{N}) \mapsto \frac{(m: \mathbb{R})^{k} \cdot (\operatorname{Nat.choose}(k^{2}) n: \mathbb{R})}{\left((m: \mathbb{R}) + 1\right)^{k + 1}}), (m: \mathbb{R}) \cdot \left(2 \cdot (m: \mathbb{R}) + 1\right) \cdot (q: \mathbb{R})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301310Divisibility.falling_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

For every positive n and natural m, the square-binomial series converges to m(2m+1) times an integer. Its finite integral numerator vanishes at zero and minus one, so it has the factor X(X+1). Homogenization preserves the integral quotient, including at m=0.

**Theorem 1.6 (Rising square-binomial geometric averages).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall m \in \mathbb{N},\; \exists q \in \mathbb{Z},\; \operatorname{HasSum}\left((fun (k: \mathbb{N}) \mapsto \frac{(m: \mathbb{R})^{k} \cdot (\operatorname{Nat.choose}(k^{2} + n - 1) n: \mathbb{R})}{\left((m: \mathbb{R}) + 1\right)^{k + 1}}), (m: \mathbb{R}) \cdot \left(2 \cdot (m: \mathbb{R}) + 1\right) \cdot (q: \mathbb{R})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301310Divisibility.rising_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

The same factorization applies to the even polynomial with natural values Nat.choose (k squared plus n minus one) n. Natural subtraction is used in the upper index. The series converges to m(2m+1) times an integer for every natural m.

**Theorem 1.7 (The divisibility theorem).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (10: \mathbb{R}) \cdot (q: \mathbb{R})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaA301310Divisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/h301310-divisibility` (proved) by `D5/S3/ArithSums/HannaA301310Divisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"h301310-divisibility","declaration_gid":"D5/S3/ArithSums/HannaA301310Divisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A301310, A301311 and A301432: geometric binomial averages*. URL: <https://oeis.org/A301310/internal>.

*Commentary.*

The convergent geometric average at m=2 is m(2m+1) times an integer, giving the factor 10. Summability is proved before identifying the infinite sum.

## References

- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.a`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.claim`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.coeff_cast`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.eval_diff_iter_apply`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.falling_hasSum`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.result`
- Truth anchor: `D5/S3/ArithSums/HannaA301310Divisibility.rising_hasSum`
