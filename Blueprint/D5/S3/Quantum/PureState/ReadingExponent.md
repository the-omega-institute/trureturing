# The reading exponent

## Abstract

A function multiplicative on [0, 1] with F(cos t) + F(sin t) = 1 on the quarter circle is the square on [0, 1], without any continuity assumption.

**Theorem 1.1 (Multiplicativity and quarter-circle normalization force the square).**

$$\forall F \in \mathbb{R} \to \mathbb{R},\; \left(\forall s \in Icc\left(0, 1\right),\; \forall t \in Icc\left(0, 1\right),\; F\left(s \cdot t\right) = F\left(s\right) \cdot F\left(t\right)\right) \Rightarrow \left(\left(\forall t \in Icc\left(0, \frac{\pi}{2}\right),\; F\left(cos\left(t\right)\right) + F\left(sin\left(t\right)\right) = 1\right) \Rightarrow \left(\forall s \in Icc\left(0, 1\right),\; F\left(s\right) = s^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/ReadingExponent.eq_sq_of_mul_of_cos_add_sin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a real function on the real line. Assume F(st) = F(s)F(t) for all s and t in [0, 1], and F(cos t) + F(sin t) = 1 for every t in [0, π/2]. Then F(s) = s² for every s in [0, 1]. No continuity, measurability or monotonicity of F is assumed, and nothing is asserted about F outside [0, 1].

Proof: since F(s) = F(√s)², F is nonnegative on [0, 1], and the normalization at the angle arccos s reads F(s) + F(√(1 − s²)) = 1, so F ≤ 1 there. The normalization at t = 0 gives F(1) + F(0) = 1, and F(0) = F(0)² = F(0)F(1) excludes F(0) = 1, so F(0) = 0 and F(1) = 1. For 0 ≤ s ≤ t ≤ 1 with t > 0, F(s) = F(t)F(s/t) ≤ F(t), so F is monotone on [0, 1]. The function G(u) = F(√u) satisfies G(u) + G(1 − u) = 1 on [0, 1] and is multiplicative there; hence G(1/2) = 1/2, and induction on n gives G(k/2ⁿ) = k/2ⁿ for 0 ≤ k ≤ 2ⁿ: a point k/2ⁿ⁺¹ with k ≤ 2ⁿ is (1/2)(k/2ⁿ), and the remaining points are reached through G(u) + G(1 − u) = 1. Monotonicity and the dyadic values give u − 1/2ⁿ < G(u) for every n; the same bound for 1 − u together with G(u) + G(1 − u) = 1 gives G(u) < u + 1/2ⁿ. Hence G(u) = u, and F(s) = G(s²) = s².

The following written argument, which is not stated as a theorem here, shows that neither hypothesis can be dropped. The polynomial 3s⁴ − 2s⁶ satisfies the normalization, since with a = cos² t and b = sin² t one has 3(a² + b²) − 2(a³ + b³) = 3(1 − 2ab) − 2(1 − 3ab) = 1, but it is not multiplicative: its value at 1/4 is 46/4096, while the square of its value at 1/2 is 100/4096. The power s ↦ sᵖ is multiplicative for every p ≥ 0, but for p ≠ 2 the normalization fails at t = π/4, where the sum is 2^(1 − p/2) ≠ 1.

The result is an elementary functional-equation argument; no published source stating it in this form is known, and nothing is claimed as new.

## References

- Truth anchor: `D5/S3/Quantum/PureState/ReadingExponent.eq_sq_of_mul_of_cos_add_sin`
