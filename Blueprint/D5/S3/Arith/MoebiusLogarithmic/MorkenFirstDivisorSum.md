# Morken's first divisor-sum identity

## Abstract

The coprime Moebius sum equals a double sum over squarefree divisors.

**Theorem 1.1 (The identity on every positive integer).**

$$\forall n\in\mathbb{N}, 0<n\Rightarrow \sum_{1 \le k \le n, \operatorname{gcd}\left(k, n\right) = 1}\operatorname{mu}\left(k\right) = \sum_{d\in\operatorname{divisors}\left(n\right), \operatorname{mu}\left(d\right)\neq0}\sum_{1 \le m \le \frac{n}{d}, \operatorname{gcd}\left(m, d\right) = 1}\operatorname{mu}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a112399-morken-first-divisor-sum` (proved) by `D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a112399-morken-first-divisor-sum","declaration_gid":"D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jamie Morken (2026). *First divisor-sum conjecture in OEIS A112399*. URL: <https://oeis.org/A112399/internal>.

*Commentary.*

Here n, k, d and m are natural numbers, and n is positive. mu is the standard integer-valued Moebius function, including mu(1)=1. All interval endpoints are inclusive. divisors(n) contains exactly the positive divisors of n, so n/d is exact integer division. The outer filter mu(d)!=0 restricts d, without imposing squarefreeness on n. The inner coprimality condition is gcd(m,d)=1, whereas the left condition is gcd(k,n)=1. No finite bound on n or assertion at n=0 is made.

OEIS A112399, revision 41, FORMULA, attributes this first conjecture to Jamie Morken. The conjecture has AI-assisted provenance; that supplies no proof. The second conjecture in the entry and the product-parameter identity associated with A372706 are separate assertions.

For positive d and m the filtered summand equals mu(d*m)*mu(d). If mu(d)=0 both expressions vanish. Otherwise d is squarefree: coprimality permits multiplicativity and mu(d)^2=1, while failure of coprimality makes d*m nonsquarefree. Reindex by k=d*m and exchange the finite sums. The coefficient of mu(k) becomes the sum of mu(d) over divisors of gcd(k,n). The standard Moebius divisor cancellation is one when gcd(k,n)=1 and zero otherwise. Thus the remaining sum is precisely the original coprime sum.

## References

- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result`
