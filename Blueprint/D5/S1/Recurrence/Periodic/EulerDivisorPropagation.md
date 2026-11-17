# A386381 Conjecture 2 for ordinary Euler numbers

## Abstract

Ordinary A000111 satisfies both complete A386381 Conjecture 2 assertions.

E denotes the source-normalized ordinary A000111 carrier with E(0)=1. Every parameter below is natural, and phi is Nat.totient. The result is an unfrozen Stage A candidate pending independent pre-freeze review; neither source exposition nor generated prose establishes publication or a resolution KPI. Odd prime powers use corrected zero transfer; the two-primary component uses the tangent bound; prime-power divisibility assembles them in the same E value.

**Theorem 1.1 (The ordinary all-positive-index local theorem).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((0 < k) \implies ((p^{r + 1} \mid \operatorname{E}\left(k\right)) \implies (p^{r + 1} \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(p^{r + 1}\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.odd_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totient is even, so both indices use the same signed branch. Each sign is a unit and therefore preserves zero divisibility.

**Theorem 1.2 (The complete main assertion).**

$$\forall k: \mathbb{N}, (\forall m: \mathbb{N}, (\forall d: \mathbb{N}, ((2 < d) \implies ((d \mid \operatorname{E}\left(k\right)) \implies (d \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(d\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the entire main source assertion, including m=0, every early index, every composite modulus and both prime-power branches. There is no eventual-period, spectrum or positivity premise.

**Theorem 1.3 (The complete particular family).**

$$\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((k \neq 3) \implies (\operatorname{E}\left(k\right) \mid \operatorname{E}\left(k + m \cdot \operatorname{totient}\left(\operatorname{E}\left(k\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Indices zero, one and two have divisor one. For k at least four the proved bound E(k)>2 allows the main assertion. Only k=3 is excluded, exactly as in the source.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.odd_prime_power`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular`
- Dependency: [D5/S1/Recurrence/Periodic/EulerSecantBridge](EulerSecantBridge.md)
- Dependency: [D5/S1/Recurrence/Periodic/EulerTwoPrimary](EulerTwoPrimary.md)
