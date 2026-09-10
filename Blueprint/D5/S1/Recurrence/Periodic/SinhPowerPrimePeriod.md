# The Prime-Period Question for OEIS A224899

## Abstract

A224899 has period p-1 modulo every odd prime, and the assertion fails at p=2.

Library note bala2022a224899 records the exponential generating function in OEIS A224899 and Peter Bala's May 29, 2022 conjecture. The sequence a is defined by its finite exponential coefficient expansion through H. The exponential generating function identity itself is not formalized. The asserted period need not be minimal.

All indices, bounds, exponents, and subtractions in exponents are natural numbers. The notation range(t) means the natural numbers strictly below t. The functions H and a take integer values; choose, factorial, and stirlingSecond denote Nat.choose, Nat.factorial, and Nat.stirlingSecond, cast to the ambient ring when multiplied. In H and the coefficient bridge all value arithmetic is integer arithmetic, including 2*j-k and the negation of k. The function div is integer division, whose exactness follows from the bridge. The notation residue(p,t) casts t to ZMod p. In the exponential sum all arithmetic outside indices, bounds, exponents, and residue arguments is in ZMod p; inv denotes the field inverse.

**Definition 1.1 (The finite exponential coefficient).**

$$\forall n, k: \mathbb{N}, \operatorname{H}\left(n, k\right) = \operatorname{div}\left(\sum_{j \in \operatorname{range}\left(k + 1\right)} ((-1)^{(k - j)} \cdot \operatorname{choose}\left(k, j\right) \cdot (k \cdot (2 \cdot j - k))^{n}), 2^{k}\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient expression expands the kth power of exp(k*x)-exp(-k*x), divided by 2^k. The sign convention (-1)^(k-j) pairs with the base k*(2*j-k).

**Theorem 1.2 (The factorial-bearing Stirling bridge).**

$$\forall n, k: \mathbb{N}, \operatorname{H}\left(n, k\right) = k^{n} \cdot \operatorname{factorial}\left(k\right) \cdot \sum_{r \in \operatorname{range}\left(n + 1\right)} (\operatorname{choose}\left(n, r\right) \cdot (-k)^{(n - r)} \cdot 2^{(r - k)} \cdot \operatorname{stirlingSecond}\left(r, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.coefficient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand (2*j-k)^n by the binomial theorem and interchange the two finite sums. Stirling inclusion-exclusion evaluates the inner alternating power sum as factorial(k)*stirlingSecond(r,k). When r is less than k this vanishes; otherwise 2^r equals 2^k times 2^(r-k). Factoring out 2^k proves that the integer division is exact and leaves the displayed factor factorial(k).

**Definition 1.3 (The sequence A224899).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (\operatorname{H}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the finite exponential coefficients over k at most n, including the constant contribution at n=0. This is the coefficient expression described in bala2022a224899.

**Theorem 1.4 (A fixed prime-sized window).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\operatorname{residue}\left(p, \operatorname{H}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If k exceeds n, every stirlingSecond(r,k) in the bridge is zero. If k is at least p, the prime p divides factorial(k), so the coefficient vanishes modulo p. Extending or truncating the finite sum therefore gives exactly range(p), even at n=0.

**Theorem 1.5 (An exponential sum independent of the index).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies p \neq 2 \implies \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right) = \sum_{k \in \operatorname{range}\left(p\right)} (\sum_{j \in \operatorname{range}\left(k + 1\right)} (\operatorname{inv}\left(2\right)^{k} \cdot ((-1)^{(k - j)} \cdot \operatorname{residue}\left(p, \operatorname{choose}\left(k, j\right)\right)) \cdot (\operatorname{residue}\left(p, k\right) \cdot (2 \cdot \operatorname{residue}\left(p, j\right) - \operatorname{residue}\left(p, k\right)))^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a_exponential_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p different from 2, the residue of 2 is nonzero. Cast the exact integer division defining H into ZMod p, invert 2^k, and distribute through the fixed window. Both the coefficients and the index sets are independent of n.

**Theorem 1.6 (Bala's assertion for every odd prime).**

$$\forall p, n: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies p \neq 2 \implies 1 \le n \implies \operatorname{residue}\left(p, \operatorname{a}\left(n + (p - 1)\right)\right) = \operatorname{residue}\left(p, \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_odd` (`✓ std3`). ∎

*Citation.* Peter Bala (2022). *OEIS A224899, e.g.f. Sum_{n>=0} sinh(n*x)^n*. URL: <https://oeis.org/A224899>.

*Commentary.*

Apply pow_add_pred_prime from AlternatingWeightStirlingPrimePeriod to each base k*(2*j-k). Positive n ensures the power identity also holds at the zero base. Summing proves the odd-prime part of the conjecture recorded in bala2022a224899.

**Definition 1.7 (The period-one claim at two).**

$$\operatorname{balaConjectureTwo}\left(\right) \iff (\forall n: \mathbb{N}, 1 \le n \implies \operatorname{residue}\left(2, \operatorname{a}\left(n + 1\right)\right) = \operatorname{residue}\left(2, \operatorname{a}\left(n\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.balaConjectureTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This names the p=2 specialization of Bala's conjecture: every residue from index one would equal the next residue.

**Theorem 1.8 (The prime two refutes the literal conjecture).**

$$\neg (\operatorname{balaConjectureTwo}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_two_false` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a224899-sinh-power-prime-period` (refuted) by `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_two_false`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a224899-sinh-power-prime-period","declaration_gid":"D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_two_false","resolution_kind":"refuted"} -->

*Citation.* Peter Bala (2022). *OEIS A224899, e.g.f. Sum_{n>=0} sinh(n*x)^n*. URL: <https://oeis.org/A224899>.

*Commentary.*

The defining finite sum gives a(1)=1 and a(2)=8. Their residues modulo 2 differ, contradicting balaConjectureTwo at n=1. This certified instance refutes the named period-one claim in bala2022a224899; combined with the odd-prime theorem, it identifies the only prime exception.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.H`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a_exponential_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.a_window`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.balaConjectureTwo`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_odd`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.bala_conjecture_two_false`
- Truth anchor: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.coefficient_bridge`
- Dependency: [D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod](AlternatingWeightStirlingPrimePeriod.md)
