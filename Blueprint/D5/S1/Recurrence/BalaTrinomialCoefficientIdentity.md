# Bala's finite-binomial coefficient identity

## Abstract

A rational formal coefficient and an inclusive finite sum of ordinary binomial coefficients.

**Definition 1.1 (The independent formal quotient).**

$$\forall n \in \mathbb{N},\; \operatorname{source}\left(n\right) = \left(1 + X + X^{2}\right)^{3 \cdot n} \cdot \operatorname{inverse}\left(\left(1 + X\right)^{2 \cdot n}\right)$$

*Formalization.* `D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.source` (`✓ std3`).

*Citation.* Peter Bala (2022). *OEIS A351858 finite-binomial coefficient identity*. URL: <https://oeis.org/A351858>.

*Commentary.*

For every natural n, source(n) is the product of (1+X+X^2) to exponent 3n and the formal multiplicative inverse of (1+X) to exponent 2n in Q[[X]]. The denominator has constant coefficient one, so it is a unit. This defines the quotient independently of the finite sum. These are formal series at zero; no analytic convergence assumption is used.

The NAME field of OEIS A351858 reads: "a(n) = [x^n] (1 + x + x^2)^(3*n)/(1 + x)^(2*n)."

**Theorem 1.2 (The coefficient identity at every natural index).**

$$\forall n \in \mathbb{N},\; \operatorname{coeff}\left(n, \operatorname{source}\left(n\right)\right) = \operatorname{natCastQ}\left(\sum_{k \in \operatorname{range}\left(\operatorname{div}\left(n, 2\right) + 1\right)} \operatorname{choose}\left(3 \cdot n, k\right) \cdot \operatorname{choose}\left(n - k, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a351858-bala-coefficient-identity` (proved) by `D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a351858-bala-coefficient-identity","declaration_gid":"D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2022). *OEIS A351858 finite-binomial coefficient identity*. URL: <https://oeis.org/A351858>.

*Commentary.*

All indices are natural, including zero and one. The displayed choose denotes Nat.choose, the ordinary natural binomial coefficient; subtraction n-k is natural subtraction. The displayed div denotes Nat.div, so div(n,2) is floor(n/2). The displayed range denotes Finset.range; range(floor(n/2)+1) includes both endpoints 0 and floor(n/2). The notation natCastQ casts the entire natural sum to Q. The left side extracts the degree-n coefficient of source(n) at zero. There is no primality, positivity, eventual-index, congruence, or truncated-series premise.

Peter Bala's FORMULA entry reads: "Conjecture: a(n) = Sum_{k = 0..floor(n/2)} C(3*n,k)*C(n-k,k)."

For positive n, formal substitution X=T/(1-T), followed by multiplication by (1-T)^(n-1), preserves the degree-n coefficient. The proof checks this using finite coefficient substitution and the coefficients of powers of the geometric series. Under this weighted substitution the source becomes (1+T^2/(1-T))^(3n)/(1-T).

The binomial expansion has terms binom(3n,k) T^(2k)/(1-T)^(k+1). The degree-n coefficient of each term is binom(3n,k) binom(n-k,k) when 2k is at most n, and zero otherwise. Thus only the inclusive range through floor(n/2) contributes. The proof treats n=0 separately, where both sides equal one; n=1 is included in the positive case. The final cast identifies the rational sum with the cast of the natural sum.

The separate supercongruence on the same sequence is outside this identity.

## References

- Truth anchor: `D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result`
- Truth anchor: `D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.source`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](Invariants/CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/MatharA000159Recurrence](Invariants/MatharA000159Recurrence.md)
