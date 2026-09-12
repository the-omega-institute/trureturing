# Totient Periods for Weighted Stirling Transforms

## Abstract

Weighted Stirling transforms have totient periods, proving A064618 and A004123.

Library note bala2018a064618 records the A064618 conjecture and note bala2022a004123 the A004123 conjecture. The former has weight k! and offset zero; the latter has weight 2^k and offset one, so its term at index n is T(k mapped to 2^k,n-1). The proved onsets are n at least m and n at least m+1, respectively. Neither onset nor period is asserted to be minimal. The broader A004123 conjecture about every e.g.f. G(exp(x)-1) is not claimed here.

All indices, range bounds, and exponent subtractions are natural numbers. The weight w maps natural numbers to integers, and T is integer-valued. The functions factorial, stirlingSecond, choose, and totient denote Nat.factorial, Nat.stirlingSecond, Nat.choose, and Nat.totient. Natural factorials and Stirling numbers in the definition of T are cast to integers. The notation range(t) means the natural numbers strictly below t; residue(m,t) is the cast of the integer or natural t to ZMod m. In the exponential sum, arithmetic outside bounds, exponents, and residue arguments is in ZMod m. The weights in the two instances take their values in the integers.

**Definition 1.1 (The weighted Stirling transform).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{T}\left(w, n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (\operatorname{w}\left(k\right) \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The summand is w(k) times k! times S(n,k), with no extra k^n factor.

**Theorem 1.2 (A fixed modulus-sized window).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall m, n: \mathbb{N}, 0 < m \implies \operatorname{residue}\left(m, \operatorname{T}\left(w, n\right)\right) = \sum_{k \in \operatorname{range}\left(m\right)} (\operatorname{residue}\left(m, \operatorname{w}\left(k\right) \cdot \operatorname{factorial}\left(k\right) \cdot \operatorname{stirlingSecond}\left(n, k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Terms beyond n vanish by the Stirling diagonal bound. For positive m, terms with k at least m vanish because m divides k!. These two facts give the fixed window for every natural index n, including zero.

**Theorem 1.3 (Exponential coefficients independent of n).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall m, n: \mathbb{N}, 0 < m \implies \operatorname{residue}\left(m, \operatorname{T}\left(w, n\right)\right) = \sum_{k \in \operatorname{range}\left(m\right)} (\sum_{j \in \operatorname{range}\left(k + 1\right)} (\operatorname{residue}\left(m, \operatorname{w}\left(k\right)\right) \cdot ((-1)^{k - j} \cdot \operatorname{residue}\left(m, \operatorname{choose}\left(k, j\right)\right)) \cdot \operatorname{residue}\left(m, j\right)^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_exponential_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public stirling2_inclusion_exclusion identity of StirlingPowerFactorialPrimePeriod expands k! times S(n,k). Distributing w(k) yields the displayed fixed double sum of powers of j.

**Theorem 1.4 (Euler and prime-power divisibility).**

$$\forall j, m, n: \mathbb{N}, 0 < m \implies m \le n \implies \operatorname{residue}\left(m, j\right)^{n + \operatorname{totient}\left(m\right)} = \operatorname{residue}\left(m, j\right)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.pow_add_totient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime power p^e dividing m, split according to whether p divides j. If it does, e is at most n because e is less than p^e, which is at most m; both powers vanish modulo p^e. Otherwise j is a unit modulo p^e, so Euler's theorem and phi(p^e) dividing phi(m) give the same congruence. Divisibility of the integer difference by every prime power dividing m implies divisibility by m.

**Theorem 1.5 (Totient period for every weight).**

$$\forall w: \mathbb{N} \to \mathbb{Z}, \forall m, n: \mathbb{N}, 0 < m \implies m \le n \implies \operatorname{residue}\left(m, \operatorname{T}\left(w, n + \operatorname{totient}\left(m\right)\right)\right) = \operatorname{residue}\left(m, \operatorname{T}\left(w, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.stirling_transform_totient_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply pow_add_totient to each base j in the fixed double sum. The coefficients do not depend on n, so the equality survives both finite sums for every integer weight. This is a sibling of the prime-period theorem with the additional k^n factor: here that factor is absent and the modulus can be composite.

**Theorem 1.6 (Bala's A064618 totient-period conjecture).**

$$\forall m, n: \mathbb{N}, 0 < m \implies m \le n \implies \operatorname{residue}\left(m, \operatorname{T}\left((k \mapsto \operatorname{factorial}\left(k\right)), n + \operatorname{totient}\left(m\right)\right)\right) = \operatorname{residue}\left(m, \operatorname{T}\left((k \mapsto \operatorname{factorial}\left(k\right)), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a064618` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a064618-stirling-transform-totient-period` (proved) by `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a064618`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a064618-stirling-transform-totient-period","declaration_gid":"D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a064618","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2018). *OEIS A064618, Stirling transform of (n!)^2*. URL: <https://oeis.org/A064618>.

*Commentary.*

Set w(k)=k!. The finite formula in bala2018a064618 is then T(w,n), and the general theorem supplies period phi(m) from n at least m.

**Theorem 1.7 (Bala's A004123 totient-period conjecture).**

$$\forall m, n: \mathbb{N}, 0 < m \implies m + 1 \le n \implies \operatorname{residue}\left(m, \operatorname{T}\left((k \mapsto 2^{k}), n + \operatorname{totient}\left(m\right) - 1\right)\right) = \operatorname{residue}\left(m, \operatorname{T}\left((k \mapsto 2^{k}), n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a004123` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a004123-generalized-weak-orders-totient-period` (proved) by `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a004123`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a004123-generalized-weak-orders-totient-period","declaration_gid":"D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a004123","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A004123, number of generalized weak orders on n points*. URL: <https://oeis.org/A004123>.

*Commentary.*

Set w(k)=2^k. The entry's term a(n) is T(w,n-1). If n is at least m+1, then n-1 is at least m and n+phi(m)-1 equals (n-1)+phi(m). The general theorem therefore gives the claimed period in the entry's own offset-one indexing.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_exponential_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_window`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a004123`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.bala_conjecture_a064618`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.pow_add_totient`
- Truth anchor: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.stirling_transform_totient_period`
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../Parity/StirlingPowerFactorialPrimePeriod.md)
