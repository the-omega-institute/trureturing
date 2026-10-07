# Differences of complex powers

## Abstract

On a complex disk of radius H, the difference of the ell-th powers is bounded by ell times the distance of the bases times H^(ell-1).

**Theorem 1.1 (Uniform power-difference bound).**

$$\forall a, b \in \mathbb{C}, \forall ell \in \mathbb{N}, \forall H \in \mathbb{R}, (hH: 0 \le H) \Rightarrow (ha: \Vert a\Vert \le H) \Rightarrow (hb: \Vert b\Vert \le H) \Rightarrow \Vert a^{ell}-b^{ell}\Vert \le (ell: \mathbb{R}) \Vert a-b\Vert H^{ell-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ComplexPowerDifference.norm_pow_sub_pow_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be complex numbers, ell a natural number, and H a nonnegative real number bounding both norms. Factor a^ell-b^ell as a-b times a sum of ell mixed powers. Each summand has norm at most H^(ell-1), so the triangle inequality gives the bound. The exponent ell-1 uses truncated natural subtraction. For ell=0 the difference and the right side both vanish.

## References

- Truth anchor: `D5/S3/AnalyticClosure/ComplexPowerDifference.norm_pow_sub_pow_le`
