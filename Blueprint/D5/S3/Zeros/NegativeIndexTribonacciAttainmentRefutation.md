# Negative-index tribonacci root-amplitude attainment

## Abstract

Mane's negative-index root-amplitude attainment fails at k = 3 and n = -15.

**Definition 1.1 (Backward polynomial recurrence).**

$$\forall k \in \operatorname{Nat},\; \forall m \in \operatorname{Nat},\; (\operatorname{a}\left(k, m\right): \operatorname{Polynomial}\left(\mathbb{Z}\right)) = \operatorname{if} (m = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{if} (k = 0 \lor m < k) \operatorname{then} 0 \operatorname{else} \operatorname{a}\left(k, m - k\right) - \sum_{j: \operatorname{Fin}\left(k - 1\right)} (X^{k - \left(\operatorname{val}\left(j\right) + 1\right)} \cdot \operatorname{a}\left(k, m - k + \operatorname{val}\left(j\right) + 1\right)))$$

*Formalization.* `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.a` (`✓ std3`).

*Citation.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

Mane, p. 2, (1.2)–(1.3): “By convention, the initial values are 𝓕_{n,k}(x) = 1 for n = 1 and 𝓕_{n,k}(x) = 0 for n ∈ [−(k−2), 0].” The recurrence is 𝓕_{n,k}(x) = x^{k−1}𝓕_{n−1,k}(x) + x^{k−2}𝓕_{n−2,k}(x) + ⋯ + 𝓕_{n−k,k}(x). Here a k m is 𝓕_{1−m,k}, with integer polynomial coefficients. The index j : Fin(k−1) enumerates the source indices j.val+1. Every subtraction between natural numbers is truncated subtraction. For k = 0 and m > 0 the value is totalized to zero, outside the source's k ≥ 2 range.

**Definition 1.2 (Source index convention).**

$$\forall k \in \operatorname{Nat},\; \forall n \in \mathbb{Z},\; \operatorname{F}\left(k, n\right) = \operatorname{a}\left(k, \operatorname{Int}.\operatorname{toNat}\left(1 - n\right)\right)$$

*Formalization.* `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.F` (`✓ std3`).

*Citation.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

Mane, p. 2, (1.3), iterates the recurrence downwards to negative indices. The displayed construction uses a k m = 𝓕_{1−m,k}; thus F k n agrees with the source polynomial for n ≤ 1. Int.toNat is the nonnegative integer-to-natural conversion. Its totalization beyond n = 1 is unused.

**Definition 1.3 (Maximum nonzero-root amplitude).**

$$\forall k \in \operatorname{Nat},\; \forall p \in \operatorname{Polynomial}\left(\mathbb{Z}\right),\; (\operatorname{zeta}\left(k, p\right): \operatorname{Real}) = \operatorname{sSup}\left(\operatorname{Set}.\operatorname{image}\left((\operatorname{fun} (z: \operatorname{Complex}) \mapsto \left\lVert z \right\rVert^{k}), \{ z: \operatorname{Complex} \mid (z \ne 0 \land \operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{Complex}\right), p\right)\right) = 0) \}\right)\right)$$

*Formalization.* `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.zeta` (`✓ std3`).

*Citation.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

Mane, p. 19: “For k ≥ 2 and n ∈ ℤ, let ζ_{n,k} denote the maximum amplitude of |x_root|^k, where P_{n,k}(x_root^k) = 0. Set ζ_{n,k} = 0 if 𝓕_{n,k}(x) has no nonzero roots, including vanishing polynomials.” The polynomial is mapped from ℤ to ℂ before evaluation; ‖z‖ is the complex norm. For a nonzero polynomial the root set is finite, so its nonempty amplitude set has a maximum. Real sSup of the empty set is zero. For the zero polynomial and k ≥ 2 the amplitude set is unbounded, and Real sSup is also zero, matching the vanishing-polynomial convention.

**Definition 1.4 (The attainment clause of Conjecture 6.6).**

$$claim \Leftrightarrow (\forall k \in \operatorname{Nat},\; (k \ge 3) \Rightarrow (\forall s \in \operatorname{Nat},\; (s \ge 1) \Rightarrow (\operatorname{zeta}\left(k, \operatorname{F}\left(k, -(\operatorname{Nat}.\operatorname{cast}\left((s \cdot k: \operatorname{Nat})\right): \mathbb{Z})\right)\right) = (\operatorname{Nat}.\operatorname{cast}\left(s\right): \operatorname{Real}))))$$

*Formalization.* `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.claim` (`✓ std3`).

*Citation.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

Mane, p. 20, Conjecture 6.6: “For fixed k ≥ 3 and n < 0, the upper bound is ζ_{n,k} ≤ ⌊|n|/k⌋. The bound is attained whenever r_{n,k} = 1 (equivalently n = −sk, where s ≥ 1), i.e. it is a tight bound.” The proposition encodes the attainment sentence for every natural k ≥ 3 and s ≥ 1, at the integer index −(s*k). The right-hand s is cast to ℝ. The universal upper-bound inequality is a separate clause.

**Theorem 1.5 (Attainment fails at the nondegenerate tribonacci instance).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mane-2026-negative-index-fibonacci-root-amplitude` (refuted) by `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mane-2026-negative-index-fibonacci-root-amplitude","declaration_gid":"D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. R. Mane (2026). *Identically vanishing k-generalized Fibonacci polynomials*. URL: <https://arxiv.org/abs/2507.11596v4>.

*Commentary.*

At k = 3 and n = −15 the recurrence gives 𝓕_{−15,3}(x) = −x(x¹² + 8x⁹ + 18x⁶ + 15x³ + 5). Writing t = x³ gives the quartic t⁴ + 8t³ + 18t² + 15t + 5. The intermediate value theorem supplies a real root −A with 4 < A < 5. Factoring out t+A leaves a monic cubic with positive coefficients b < 4, c < 3 and d < 5/4. The polynomial Cauchy bound puts all its roots strictly inside radius 5. Thus every nonzero root x of the tribonacci polynomial satisfies ‖x‖³ < 5. Its amplitude set is finite and nonempty, so ζ is strictly less than 5. The proposed equality at s = 5 therefore fails. The upper-bound inequality holds at this instance; its general validity is not asserted.

## References

- Truth anchor: `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.F`
- Truth anchor: `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.a`
- Truth anchor: `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.claim`
- Truth anchor: `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result`
- Truth anchor: `D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.zeta`
