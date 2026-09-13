# The Least Self-Divisor Exponent

## Abstract

The least self-divisor exponent in OEIS A092028 is the least prime factor of n minus one.

**Definition 1.1 (The A092028 sequence).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = sInf\left(\{m \in \mathbb{N} \mid (1 < m) \land (m \mid n^{m} - 1)\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.a` (`✓ std3`).

*Citation.* Farideh Firoozbakht (2004). *OEIS A092028, a(n) is the smallest m > 1 such that m divides n^m-1*. URL: <https://oeis.org/A092028>.

*Commentary.*

In the natural numbers, `sInf` selects the least element of the set, and `sInf` of the empty set is zero. For n greater than two, the defining set is nonempty. Every subtraction in the formula is truncated natural-number subtraction.

**Theorem 1.2 (Firoozbakht's second conjecture).**

$$\forall n \in \mathbb{N},\; (2 < n) \Rightarrow (a\left(n\right) = minFac\left(n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a092028-least-self-divisor-power-minus-one` (proved) by `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a092028-least-self-divisor-power-minus-one","declaration_gid":"D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The upper bound uses p=minFac(n-1), since p divides n-1 and therefore p divides n^p-1. For the lower bound, take q=minFac(m). The multiplicative order of n modulo q divides both m and q-1; minimality of q makes those integers coprime, so the order is one and q divides n-1. Firoozbakht's first conjecture follows because minFac(n-1) is prime when n is greater than two.

## References

- Truth anchor: `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.a`
- Truth anchor: `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.firoozbakht_a092028`
