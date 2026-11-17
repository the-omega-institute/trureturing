# Reusing the existing secant carrier

## Abstract

The even ordinary Euler subsequence is the existing A000364 carrier.

a is the existing integer A000364 carrier in SecantNumberPurePeriodRefutation. E is ordinary A000111. The exponential identity gives the inverse hyperbolic cosine convolution; its even coefficients, combined with the exact ordinary sign bridge, satisfy the original secant recurrence. The existing a_unique theorem identifies the carriers.

**Theorem 1.1 (Exact A000364 correspondence).**

$$\forall s: \mathbb{N}, (\operatorname{E}\left(2 \cdot s\right) = \operatorname{a}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSecantBridge.secant_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality is in the integers, with the natural E value cast. No independent secant carrier is introduced.

**Theorem 1.2 (All small-value boundaries).**

$$(\operatorname{E}\left(0\right) = 1) \land ((\operatorname{E}\left(1\right) = 1) \land ((\operatorname{E}\left(2\right) = 1) \land ((\operatorname{E}\left(3\right) = 2) \land (\forall k: \mathbb{N}, ((4 \le k) \implies (2 < \operatorname{E}\left(k\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSecantBridge.boundary_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source recurrence gives the initial values, and its zeroth summand proves monotonicity.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSecantBridge.boundary_values`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSecantBridge.secant_bridge`
- Dependency: [D5/S1/Recurrence/Periodic/EulerUpDownSource](EulerUpDownSource.md)
- Dependency: [D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation](SecantNumberPurePeriodRefutation.md)
