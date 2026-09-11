# Prime Periods of the Weighted Stirling Power Sum

## Abstract

Bala's A338040 conjecture: p - 1 is a period modulo every prime p.

Library note bala2022a338040 records Peter Bala's May 31, 2022 conjecture in Vaclav Kotesovec's OEIS A338040 entry. The entry defines the sequence by an exponential generating function and states the finite formula used here. The exponential generating function identity is not separately formalized. The asserted period need not be minimal.

All indices and subtraction are natural. The function stirlingSecond is Mathlib's Nat.stirlingSecond, factorial is Nat.factorial, and range(t) consists of natural numbers strictly below t. The notation residue(p,t) is the natural-number cast of t to ZMod p. The definition of a is natural-valued; the three theorem equalities are in ZMod p.

**Definition 1.1 (The OEIS finite formula).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (4^{k} \cdot k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the entry's offset-zero finite formula, including the weight 4^k.

**Theorem 1.2 (A fixed weighted window modulo each prime).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\operatorname{residue}\left(p, 4^{k} \cdot k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.a_eq_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n+1 is at most p, the added terms vanish by the Stirling diagonal bound. When p is at most n+1, the removed terms vanish modulo p because p divides k! for k at least p. Multiplication by 4^k preserves these zero terms. The result holds also at index zero.

**Theorem 1.3 (Bala's prime-period conjecture).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a338040-weighted-stirling-power-prime-period` (proved) by `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a338040-weighted-stirling-power-prime-period","declaration_gid":"D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A338040 (Kotesovec 2020), conjecture: a(n) mod p purely periodic with period p − 1*. URL: <https://oeis.org/A338040>.

*Commentary.*

The inclusion-exclusion theorem in StirlingPowerFactorialPrimePeriod turns the window into a double sum with summands 4^k (-1)^(k-j) choose(k,j) (k*j)^n in ZMod p. The weights are independent of n. Fermat's little theorem gives period p-1 for nonzero bases; both powers vanish for zero bases at positive indices. Summing proves the equality for every prime p and every positive n.

**Theorem 1.4 (Every multiple of the period).**

$$\forall p, n, m: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + m \cdot (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on m applies the prime-period equality at the positive index n+m(p-1), proving preservation by every nonnegative multiple of p-1.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.a_eq_window`
- Truth anchor: `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture`
- Truth anchor: `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.bala_conjecture_periodic`
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../Parity/StirlingPowerFactorialPrimePeriod.md)
