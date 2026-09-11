# Prime Periods of the Stirling Power-Factorial Sum

## Abstract

Bala's A122399 conjecture: p - 1 is a period modulo every prime p.

Library note bala2022a122399 records Peter Bala's May 31, 2022 conjecture in Vladeta Jovovic's OEIS A122399 entry. This is Tier 1 by the conjecture's 2022 date. The asserted period need not be minimal.

All indices and subtraction in indices or exponents are natural. The function stirlingSecond is Mathlib's Nat.stirlingSecond, factorial is Nat.factorial, choose is Nat.choose, and range(t) is the set of natural numbers strictly below t. The notation castZ denotes the natural-number cast to the integers; residue(p,t) denotes the natural-number cast of t to ZMod p. The inclusion-exclusion identity is an integer identity, the definition of a is natural-valued, and the last three equalities are in ZMod p.

**Theorem 1.1 (Weighted Stirling inclusion-exclusion).**

$$\forall n, k: \mathbb{N}, \operatorname{castZ}\left(\operatorname{factorial}\left(k\right)\right) \cdot \operatorname{castZ}\left(\operatorname{stirlingSecond}\left(n, k\right)\right) = \sum_{j \in \operatorname{range}\left(k + 1\right)} ((-1)^{k - j} \cdot \operatorname{castZ}\left(\operatorname{choose}\left(k, j\right)\right) \cdot \operatorname{castZ}\left(j\right)^{n})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binomial theorem gives the identity at n=0. The identity choose(k,j)(k+1)=choose(k+1,j)(k+1-j) makes the alternating sum satisfy the factorial-weighted Stirling recurrence. Induction on n, including the k=0 boundary, proves the formula for every n and k.

**Definition 1.2 (The OEIS finite sum).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This natural-valued finite sum is exactly the NAME in OEIS A122399, including its offset-zero convention.

**Theorem 1.3 (A fixed window modulo each prime).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\operatorname{residue}\left(p, k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.a_eq_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n+1 is at most p, the added terms vanish because the Stirling numbers vanish above the diagonal. When p is at most n+1, the removed terms vanish modulo p because p divides k! for k at least p. This identity holds even at n=0.

**Theorem 1.4 (Bala's prime-period conjecture).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a122399-stirling-power-factorial-prime-period` (proved) by `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a122399-stirling-power-factorial-prime-period","declaration_gid":"D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A122399 (Jovovic 2006), conjecture: a(n) mod p is purely periodic with period p - 1*. URL: <https://oeis.org/A122399>.

*Commentary.*

Inclusion-exclusion turns the fixed window into a double sum whose summands are (-1)^(k-j) choose(k,j) (k*j)^n in ZMod p. For nonzero bases, Fermat's little theorem gives period p-1. For zero bases, both positive powers vanish. Summing gives the conjectured equality for every positive n and every prime p.

**Theorem 1.5 (Every multiple of the period).**

$$\forall p, n, m: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + m \cdot (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on m repeatedly applies the prime-period theorem at the positive index n+m(p-1). Thus the sequence is purely periodic on positive indices with period p-1; minimality is not asserted.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.a`
- Truth anchor: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.a_eq_window`
- Truth anchor: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.bala_conjecture_periodic`
- Truth anchor: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion`
