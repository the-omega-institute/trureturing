# A386381 Conjecture 2 for ordinary Euler numbers

## Abstract

Ordinary A000111 satisfies both complete A386381 Conjecture 2 assertions.

Corrected Euler coefficients propagate zeros at every positive odd-prime-power index.

Write q=p raised to r+1, and epsilon=(-1) raised to b times floor(p/2). All parameters are natural; b is zero or one. Residue arithmetic is in ZMod q. The deleted frequencies form an exact finite bijection. The correction factor is a unit at every positive index, including indices smaller than r+1. This reconstructs a consequence of Young's prior Kummer congruence, without a p-adic premise.

**Theorem 1.1 (The prime-deleted frequency identity).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall b: \mathbb{N}, (\forall j: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((b \le 1) \implies (\left(1 - \operatorname{residue}\left(p^{r + 1}, (-1)\right)^{b \cdot \operatorname{div}\left(p, 2\right)} \cdot \operatorname{residue}\left(p^{r + 1}, p\right)^{j}\right) \cdot \operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, j\right)\right) = \sum_{h \in \operatorname{filter}\left(\operatorname{range}\left(p^{r + 1}\right), h \mapsto \neg (p \mid 2 \cdot h + b)\right)} (\operatorname{residue}\left(p^{r + 1}, (-1)\right)^{h} \cdot \operatorname{residue}\left(p^{r + 1}, 2 \cdot h + b\right)^{j}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.corrected_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the p-scaled shorter odd-length sum from the full sum. The divisible frequencies have h=p*v+b*floor(p/2).

**Theorem 1.2 (Every positive signed zero transfers).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall b: \mathbb{N}, (\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((b \le 1) \implies ((0 < k) \implies ((\operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, k\right)\right) = 0) \implies (\operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, k + m \cdot \operatorname{totient}\left(p^{r + 1}\right)\right)\right) = 0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.signed_zero_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every retained frequency is a unit. Euler periodicity equates their powers, and nilpotence of p proves the correction factor invertible.

E denotes the source-normalized ordinary A000111 carrier with E(0)=1. Every parameter below is natural, and phi is Nat.totient. Odd prime powers use corrected zero transfer; the two-primary component uses the tangent bound; prime-power divisibility assembles them in the same E value.

**Theorem 1.3 (The ordinary all-positive-index local theorem).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((0 < k) \implies ((p^{r + 1} \mid \operatorname{E}\left(k\right)) \implies (p^{r + 1} \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(p^{r + 1}\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.odd_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totient is even, so both indices use the same signed branch. Each sign is a unit and therefore preserves zero divisibility.

**Theorem 1.4 (The complete main assertion).**

$$\forall k: \mathbb{N}, (\forall m: \mathbb{N}, (\forall d: \mathbb{N}, ((2 < d) \implies ((d \mid \operatorname{E}\left(k\right)) \implies (d \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(d\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a386381-ordinary-euler-totient-propagation` (proved) by `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation` and `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386381-ordinary-euler-totient-propagation","declaration_gid":"D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386381-ordinary-euler-totient-propagation","declaration_gid":"D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

This is the entire main source assertion, including m=0, every early index, every composite modulus and both prime-power branches. There is no eventual-period, spectrum or positivity premise.

**Theorem 1.5 (The complete particular family).**

$$\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((k \neq 3) \implies (\operatorname{E}\left(k\right) \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(\operatorname{E}\left(k\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Indices zero, one and two have divisor one. For k at least four the proved bound E(k)>2 allows the main assertion. Only k=3 is excluded, exactly as in the source.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.corrected_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.odd_prime_power`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.signed_zero_transfer`
- Dependency: [D5/S1/Recurrence/Periodic/EulerSecantBridge](EulerSecantBridge.md)
- Dependency: [D5/S1/Recurrence/Periodic/EulerTwoPrimary](EulerTwoPrimary.md)
