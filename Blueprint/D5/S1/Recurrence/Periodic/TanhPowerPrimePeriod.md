# Odd-Prime Periods of the A221077 Double Stirling Formula

## Abstract

The double Stirling formula has period p-1 at every odd prime and fails at p=2.

Library note bala2022a221077 quotes the exponential generating function and Peter Bala's conjecture for OEIS A221077. The function a here takes the derived finite formula (9) as its definition, with a(0)=1. The link to the exponential generating function is derived in the note but is not formalized. The period results below concern this finite formula, and do not assert that p-1 is a minimal period.

All indices, bounds, and subtractions in exponents and factorial arguments are natural numbers. The function a is natural-valued. The symbols stirlingSecond, factorial, and choose denote Nat.stirlingSecond, Nat.factorial, and Nat.choose. The set Ico(1,t) consists of 1 through t-1, and range(t) consists of 0 through t-1. The notation residue(p,t) denotes the cast of t through the integers to ZMod p. In the window and exponential sum, arithmetic outside bounds, exponents, and residue arguments is in ZMod p; inv denotes its inverse operation. The symbol twoClaim names the proposition bala_conjecture_two.

**Definition 1.1 (The defining double Stirling formula).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} \sum_{m \in \operatorname{Ico}\left(1, n + 1\right)} (2^{n - m} \cdot \operatorname{factorial}\left(m\right) \cdot \operatorname{factorial}\left(m - 1\right) \cdot \operatorname{stirlingSecond}\left(n, m\right) \cdot \operatorname{stirlingSecond}\left(n + 1, m\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-index sum is formula (9) in bala2022a221077. At index zero the value is one.

**Theorem 1.2 (A fixed prime window).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{m \in \operatorname{Ico}\left(1, p\right)} (2^{n - m} \cdot \operatorname{residue}\left(p, \operatorname{factorial}\left(m\right)\right) \cdot \operatorname{residue}\left(p, \operatorname{factorial}\left(m - 1\right)\right) \cdot \operatorname{residue}\left(p, \operatorname{stirlingSecond}\left(n, m\right)\right) \cdot \operatorname{residue}\left(p, \operatorname{stirlingSecond}\left(n + 1, m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When m exceeds n, stirlingSecond(n,m) vanishes. When m is at least p, p divides factorial(m). Extending or restricting the sum therefore leaves exactly Ico(1,p), for every prime p and positive n.

**Theorem 1.3 (A fixed triple sum of powers).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies p \neq 2 \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{m \in \operatorname{Ico}\left(1, p\right)} (\sum_{j \in \operatorname{range}\left(m + 1\right)} (\sum_{k \in \operatorname{range}\left(m + 1\right)} ((\operatorname{inv}\left(2\right)^{m} \cdot \operatorname{inv}\left(\operatorname{residue}\left(p, m\right)\right) \cdot ((-1)^{m - j} \cdot \operatorname{residue}\left(p, \operatorname{choose}\left(m, j\right)\right)) \cdot ((-1)^{m - k} \cdot \operatorname{residue}\left(p, \operatorname{choose}\left(m, k\right)\right)) \cdot \operatorname{residue}\left(p, k\right)) \cdot (2 \cdot \operatorname{residue}\left(p, j\right) \cdot \operatorname{residue}\left(p, k\right))^{n})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a_exponential_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m in Ico(1,p), factorial(m-1) equals inv(residue(p,m)) times residue(p,factorial(m)). If m is at most n, the power of two splits into its n-th power times the m-th power of its inverse; otherwise stirlingSecond(n,m) is zero. Expand both factorial-weighted Stirling factors by stirling2_inclusion_exclusion, distribute both finite sums, and combine the powers into the base 2*residue(p,j)*residue(p,k).

**Theorem 1.4 (Bala's period at every odd prime).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies p \neq 2 \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_odd` (`✓ std3`). ∎

*Citation.* Peter Bala (2022). *OEIS A221077, e.g.f. Sum_{n>=0} tanh(n*x)^n*. URL: <https://oeis.org/A221077>.

*Commentary.*

Apply the frozen pow_add_pred_prime theorem to each base in the fixed triple sum. Its coefficients are independent of n. Thus the odd-prime part of the conjecture in bala2022a221077 holds for formula (9).

**Definition 1.5 (The named prime-two claim).**

$$\operatorname{twoClaim} \iff (\forall n: \mathbb{N}, 1 \le n \implies \operatorname{residue}\left(2, \operatorname{a}\left(n + (2 - 1)\right)\right) = \operatorname{residue}\left(2, \operatorname{a}\left(n\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two` (`✓ std3`).

*Citation.* Peter Bala (2022). *OEIS A221077, e.g.f. Sum_{n>=0} tanh(n*x)^n*. URL: <https://oeis.org/A221077>.

*Commentary.*

This proposition is the p=2 instance of the conjectured period for formula (9); the period is 2-1.

**Theorem 1.6 (Refutation at the prime two).**

$$\neg \operatorname{twoClaim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two_false` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a221077-tanh-power-prime-period` (refuted) by `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two_false`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a221077-tanh-power-prime-period","declaration_gid":"D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two_false","resolution_kind":"refuted"} -->

*Citation.* Peter Bala (2022). *OEIS A221077, e.g.f. Sum_{n>=0} tanh(n*x)^n*. URL: <https://oeis.org/A221077>.

*Commentary.*

Specialize twoClaim to n=1. The defining sum gives a(1)=1 and a(2)=8. Their residues modulo 2 differ, so the claimed period one fails.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a_exponential_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.a_window`
- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_odd`
- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two`
- Truth anchor: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two_false`
- Dependency: [D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod](AlternatingWeightStirlingPrimePeriod.md)
