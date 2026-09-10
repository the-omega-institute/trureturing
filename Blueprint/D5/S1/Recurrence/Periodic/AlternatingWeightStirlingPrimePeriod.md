# Prime Periods for Integer-Weighted Stirling Sums

## Abstract

Integer-weight Stirling power sums have prime periods, proving Bala's A220181 conjecture.

Library note bala2022a220181 records the NAME and finite FORMULA of OEIS A220181 and Peter Bala's June 1, 2022 conjecture. The sequence here is defined by that finite formula. The exponential generating function identity is not separately formalized. The period p-1 is not asserted to be minimal.

All indices, range bounds, and subtractions in exponents are natural numbers. The weight w maps natural numbers to integers. The functions aw and a are integer-valued; stirlingSecond, choose, and factorial denote Nat.stirlingSecond, Nat.choose, and Nat.factorial, cast to the ambient ring when multiplied. The notation range(t) means the natural numbers strictly below t, and residue(p,t) means the cast of the integer or natural t to ZMod p. In the exponential sum all arithmetic outside range bounds, exponents, and residue arguments is in ZMod p. The alternating-weight identity is in the integers.

**Definition 1.1 (The arbitrary integer-weight sum).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{aw}\left(w, n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (\operatorname{w}\left(k\right) \cdot k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight depends only on the summation index k.

**Theorem 1.2 (A fixed prime-sized window).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \operatorname{residue}\left(p, \operatorname{aw}\left(w, n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\operatorname{residue}\left(p, \operatorname{w}\left(k\right) \cdot k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Terms beyond n vanish by the Stirling diagonal bound. Terms with k at least p vanish modulo p because p divides k!. Either zero remains zero after multiplication by any integer weight. This gives the same fixed window also at n=0.

**Theorem 1.3 (Index-independent exponential coefficients).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \operatorname{residue}\left(p, \operatorname{aw}\left(w, n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\sum_{j \in \operatorname{range}\left(k + 1\right)} (\operatorname{residue}\left(p, \operatorname{w}\left(k\right)\right) \cdot ((-1)^{(k - j)} \cdot \operatorname{residue}\left(p, \operatorname{choose}\left(k, j\right)\right)) \cdot (\operatorname{residue}\left(p, k\right) \cdot \operatorname{residue}\left(p, j\right))^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_exponential_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public stirling2_inclusion_exclusion identity of StirlingPowerFactorialPrimePeriod expands the factorial-weighted Stirling number. Distributing the weight and combining k^n with j^n gives the base k*j and a coefficient independent of n.

**Theorem 1.4 (Prime periods of positive powers).**

$$\forall p: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \forall x: \operatorname{ZMod}\left(p\right), \forall n: \mathbb{N}, 1 \le n \implies x^{n + (p - 1)} = x^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.pow_add_pred_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero base Fermat's little theorem gives x^(p-1)=1. For the zero base both powers vanish because n is positive.

**Theorem 1.5 (Prime period for every integer weight).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{aw}\left(w, n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{aw}\left(w, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_prime_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the positive-power identity to each base k*j in the fixed double sum. Its coefficients are independent of n, so summing preserves the equality for every integer-valued weight.

**Theorem 1.6 (Every multiple for every weight).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall p, n, m: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{aw}\left(w, n + m \cdot (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{aw}\left(w, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_prime_period_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on m applies aw_prime_period at the positive index n+m(p-1).

**Definition 1.7 (The finite formula for A220181).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} ((-1)^{(n - k)} \cdot k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the offset-zero finite formula recorded in bala2022a220181, including the sign (-1)^(n-k).

**Theorem 1.8 (The alternating-weight identity).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = (-1)^{n} \cdot \operatorname{aw}\left((k \mapsto (-1)^{k}), n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.a_eq_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k in range(n+1), k is at most n. Thus (-1)^n times (-1)^k equals (-1)^(n-k), since the remaining factor (-1)^(2*k) is one. Distribute (-1)^n through the finite sum.

**Theorem 1.9 (Bala's A220181 prime-period conjecture).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a220181-alternating-weight-stirling-prime-period` (proved) by `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a220181-alternating-weight-stirling-prime-period","declaration_gid":"D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A220181, e.g.f. Sum_{n>=0} (1 - exp(-n*x))^n*. URL: <https://oeis.org/A220181>.

*Commentary.*

Use aw_prime_period with the integer weight k mapped to (-1)^k and the alternating-weight identity. When p=2 the sign is one in ZMod 2. For every other prime, p-1 is even, so the sign factor is unchanged. This proves the conjecture in bala2022a220181.

**Theorem 1.10 (Every multiple of the A220181 period).**

$$\forall p, n, m: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + m \cdot (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on m applies bala_conjecture at n+m(p-1), which remains positive.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.a_eq_alternating`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_exponential_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_prime_period`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_prime_period_multiple`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.aw_window`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.bala_conjecture_periodic`
- Truth anchor: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.pow_add_pred_prime`
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../Parity/StirlingPowerFactorialPrimePeriod.md)
