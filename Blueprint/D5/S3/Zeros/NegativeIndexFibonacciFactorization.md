# Negative-index generalized Fibonacci factorization

## Abstract

Mane's negative-index factorization holds for all k >= 2 and 2 <= s <= k+1.

**Definition 1.1 (Conjecture 6.4).**

$$claim \Leftrightarrow (\forall k \in \operatorname{Nat},\; (2 \le k) \Rightarrow (\forall s \in \operatorname{Nat},\; (2 \le s) \Rightarrow ((s \le k + 1) \Rightarrow (\operatorname{F}\left(k, -(\operatorname{Nat}.\operatorname{cast}\left((s \cdot k: \operatorname{Nat})\right): \mathbb{Z})\right) = -X \cdot (X^{k} + 1)^{s - 2} \cdot (X^{k} + \operatorname{C}\left((\operatorname{Nat}.\operatorname{cast}\left(s\right): \mathbb{Z})\right))))))$$

*Formalization.* `D5/S3/Zeros/NegativeIndexFibonacciFactorization.claim` (`✓ std3`).

*Citation.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

Mane, p. 19, Section 6: “Conjecture 6.4. Numerical calculations and symbolic manipulations yield the following. For k ≥ 2 and n = −sk, where s ∈ [2, k + 1] (the pattern fails for s ≥ k + 2), 𝓕_{−sk,k}(x) = −x(x^k + 1)^{s−2}(x^k + s). (6.4) Hence 𝓕_{−sk,k}(x) has roots x^k = −s. The case s = 2 was derived in the enumerated list following eq. (3.2).” Here k and s are natural numbers; the negative index is the integer negative of their natural product. F is the polynomial in ℤ[X] defined in NegativeIndexTribonacciAttainmentRefutation, with F k n = a k (1−n).toNat and a k m = 𝓕_{1−m,k}. The initial values and backward recurrence are those of (1.2)–(1.3). X is the polynomial indeterminate, C is Polynomial.C, and the coefficient s is cast to ℤ. The exponent s−2 uses natural truncated subtraction; 2 ≤ s makes it the ordinary nonnegative difference. The formula encodes the identity throughout the stated range; the neighbouring root and failure sentences describe its consequences and boundary.

**Theorem 1.2 (The factorization holds throughout the conjectured range).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NegativeIndexFibonacciFactorization.result` (`✓ std3`). ∎

*Resolves.* `Problems/mane-2026-negative-index-fibonacci-factorization` (proved) by `D5/S3/Zeros/NegativeIndexFibonacciFactorization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mane-2026-negative-index-fibonacci-factorization","declaration_gid":"D5/S3/Zeros/NegativeIndexFibonacciFactorization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

For the backward sequence, the generating function is (1−X^k z^k)/(1−(1+X^k)z^k+Xz^{k+1}). A finite geometric sum computes its coefficient at z^{sk+1}, because the omitted tail starts in degree k(s+1). The r-th summand has degrees between kr and (k+1)r. With s ≤ k+1, only r=s contributes to degree sk+1, and only r=s−1 contributes to degree (s−1)k+1. Subtracting X^k times the second coefficient from the first gives the displayed factorization for every permitted k and s.

## References

- Truth anchor: `D5/S3/Zeros/NegativeIndexFibonacciFactorization.claim`
- Truth anchor: `D5/S3/Zeros/NegativeIndexFibonacciFactorization.result`
- Dependency: [D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation](NegativeIndexTribonacciAttainmentRefutation.md)
