# Shannon Elasticity Certificate

## Abstract

The Shannon elasticity is strictly increasing, so its multiplicative slope ratios are strictly decreasing.

This module treats alpha = 1 directly using natural-log binary entropy. The pinned Mathlib defines artanh by a logarithm and supplies its positivity and half-log representation. The derivative is obtained from that representation locally on (-1,1). No limiting identification with the non-Shannon power formula is used.

**Definition 1.1 (Shannon elasticity).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E`

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(t) = t / ((1-t^2) artanh(t))

The defining expression is a total real function. Its derivative and sign arguments use 0 < t < 1.

**Theorem 1.2 (Derivative of inverse hyperbolic tangent).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.artanh_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.artanh_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

-1 < t < 1 → HasDerivAt artanh (1/(1-t^2)) t

The half-log formula and the quotient and logarithm derivative rules give the derivative.

**Theorem 1.3 (A lower bound for inverse hyperbolic tangent).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.self_le_artanh`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.self_le_artanh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

0 < t < 1 → t ≤ artanh(t)

The derivative of artanh(t)-t is nonnegative on [0,t], and its value at zero is zero.

**Theorem 1.4 (Derivative of Shannon elasticity).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

0 < t < 1 → HasDerivAt E (((1+t^2)artanh(t)-t)/((1-t^2)artanh(t))^2) t

The quotient rule gives the derivative. Its numerator is positive because artanh(t) >= t and t^2 artanh(t) > 0.

**Theorem 1.5 (Strict monotonicity of Shannon elasticity).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_strictMonoOn`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StrictMonoOn E (Ioo 0 1)

The derivative is strictly positive throughout the interval. The real mean value theorem gives strict monotonicity.

**Theorem 1.6 (Strict decrease of Shannon slope ratios).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.slope_ratio_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.slope_ratio_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

0 < v < 1 → StrictAntiOn (t ↦ v artanh(vt)/artanh(t)) (Ioo 0 1)

The derivative factors as v artanh(vt)/(t artanh(t)) times E(vt)-E(t). Its first factor is positive and its second factor is negative. This is the slope comparison consumed by entropy-coordinate convexity.

**Theorem 1.7 (Derivative of binary Shannon entropy in bias coordinates).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.binEntropy_bias_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.binEntropy_bias_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

0 < t < 1 → HasDerivAt (s ↦ binEntropy((1-s)/2)) (-artanh(t)) t

Mathlib's binary entropy derivative and the affine change of coordinates give minus artanh(t). This supplies the Shannon branch independently of the real-power derivative formulas.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.E_strictMonoOn`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.artanh_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.binEntropy_bias_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.self_le_artanh`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinShannonBranch.slope_ratio_strictAntiOn`
