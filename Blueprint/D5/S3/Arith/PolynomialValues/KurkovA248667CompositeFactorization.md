# Kurkov's Composite-Term Factorization Conjecture

## Abstract

Every composite term of A248667 is a product of two terms with indices greater than one.

**Definition 1.1 (The unreduced numerator polynomial).**

$$\forall n \in \mathbb{N},\; \operatorname{sourcePolynomial}\left(n\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(n\right)} \prod_{i \in \operatorname{Finset}.\operatorname{Ico}\left(j + 1, n\right)} (\operatorname{Polynomial}.\operatorname{C}\left((n: \mathbb{Z})\right) \cdot \operatorname{Polynomial}.\operatorname{X} + \operatorname{Polynomial}.\operatorname{C}\left((i: \mathbb{Z})\right))$$

*Formalization.* `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.sourcePolynomial` (`✓ std3`).

*Citation.* Clark Kimberling; Mikhail Kurkov (2014). *OEIS A248667: primitive numerator polynomials and Kurkov's composite-term conjecture*. URL: <https://oeis.org/A248667>.

*Commentary.*

OEIS A248667, COMMENTS paragraph 1 (electronic entry, no page number): The polynomial p(n,x) is defined as the numerator when the sum 1 + 1/(n*x + 1) + 1/((n*x + 1)(n*x + 2)) + ... + 1/((n*x + 1)(n*x + 2)...(n*x + n - 1)) is written as a fraction with denominator (n*x + 1)(n*x + 2)...(n*x + n - 1). For more, see A248664. The integer polynomial is the sum of the remaining tails after multiplication by that full denominator. Finset.range n contains j with 0 <= j < n; Finset.Ico (j+1) n contains i with j+1 <= i < n. Empty products are one. Polynomial.C and Polynomial.X are the constant polynomial and indeterminate over the integers. The displayed casts of n and i have type Z. At n=0 the sum is empty.

**Definition 1.2 (The increasing source sequence).**

$$\forall a \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsSourceSequence}\left(a\right) \Leftrightarrow \left(a\left(0\right) = 0 \land \left(\operatorname{StrictMono}\left(a\right) \land \left(\forall n \in \mathbb{N},\; \left(\exists k \in \mathbb{N},\; 0 < k \land a\left(k\right) = n\right) \Leftrightarrow \left(0 < n \land \operatorname{Polynomial}.\operatorname{IsPrimitive}\left(\operatorname{sourcePolynomial}\left(n\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.IsSourceSequence` (`✓ std3`).

*Citation.* Clark Kimberling; Mikhail Kurkov (2014). *OEIS A248667: primitive numerator polynomials and Kurkov's composite-term conjecture*. URL: <https://oeis.org/A248667>.

*Commentary.*

OEIS A248667, NAME: Numbers k for which coefficients of the polynomial p(k,x) defined in Comments are relatively prime. The entry has offset 1,2 and states: so that a(1) = 1 and a(2) = 3. Polynomial.IsPrimitive expresses coefficient gcd one over Z. The map a : N -> N is strictly increasing and enumerates exactly the positive n with primitive sourcePolynomial n. The auxiliary value a(0)=0 lies outside the positive index range.

**Definition 1.3 (Kurkov's conjecture).**

$$claim = \left(\left(\exists a \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsSourceSequence}\left(a\right)\right) \land \left(\forall a \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsSourceSequence}\left(a\right) \Rightarrow \left(\forall k \in \mathbb{N},\; 0 < k \Rightarrow \left(1 < a\left(k\right) \Rightarrow \left(\left(\neg \operatorname{Nat}.\operatorname{Prime}\left(a\left(k\right)\right)\right) \Rightarrow \left(\exists i \in \mathbb{N},\; \exists j \in \mathbb{N},\; 1 < i \land \left(1 < j \land a\left(k\right) = a\left(i\right) \cdot a\left(j\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.claim` (`✓ std3`).

*Citation.* Clark Kimberling; Mikhail Kurkov (2014). *OEIS A248667: primitive numerator polynomials and Kurkov's composite-term conjecture*. URL: <https://oeis.org/A248667>.

*Commentary.*

OEIS A248667, COMMENTS paragraph 3 (electronic entry, no page number): Conjecture: any composite term can be represented as a product a(i)*a(j) (i > 1, j > 1) in at least one way. - _Mikhail Kurkov_, Apr 09 2022 Composite means greater than one and not Nat.Prime. Both factor indices exceed one; they may be equal. The existence clause establishes that the exact increasing source sequence exists, and the factorization holds for every such sequence and every positive index.

**Theorem 1.4 (Every composite source term factors internally).**

$$\left(\exists a \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsSourceSequence}\left(a\right)\right) \land \left(\forall a \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsSourceSequence}\left(a\right) \Rightarrow \left(\forall k \in \mathbb{N},\; 0 < k \Rightarrow \left(1 < a\left(k\right) \Rightarrow \left(\left(\neg \operatorname{Nat}.\operatorname{Prime}\left(a\left(k\right)\right)\right) \Rightarrow \left(\exists i \in \mathbb{N},\; \exists j \in \mathbb{N},\; 1 < i \land \left(1 < j \land a\left(k\right) = a\left(i\right) \cdot a\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result` (`✓ std3`). ∎

*Resolves.* `Problems/kurkov-a248667` (proved) by `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kurkov-a248667","declaration_gid":"D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Mikhail Kurkov (2014). *OEIS A248667: primitive numerator polynomials and Kurkov's composite-term conjecture*. URL: <https://oeis.org/A248667>.

*Commentary.*

A prime dividing all coefficients must divide the leading coefficient n^(n-1), hence n. Reduction modulo a prime divisor resets the numerator recurrence to the same value at p-1. Membership therefore depends only on the prime divisors of n and is preserved by positive divisors. Every power of three belongs, so an increasing exact enumeration exists. Its first positive term is one. A composite member splits as p*q with p prime and p,q greater than one; both divisors belong and their indices exceed one.

## References

- Truth anchor: `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.IsSourceSequence`
- Truth anchor: `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.claim`
- Truth anchor: `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result`
- Truth anchor: `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.sourcePolynomial`
