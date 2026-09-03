# Right Half-Strip Riemann Reduction

## Abstract

Right half-strip zero-freeness implies the Riemann hypothesis by zeta reflection.

**Theorem 1.1 (Right half-strip zero-freeness implies the Riemann hypothesis).**

$$\left(\forall rho \in \mathbb{C},\; \operatorname{riemannZeta}\left(rho\right) = 0 \Rightarrow \left(\frac{1}{2} < \Re (rho) \Rightarrow \left(\Re (rho) < 1 \Rightarrow False\right)\right)\right) \Rightarrow \operatorname{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeta functional equation reflects every zero strictly left of the critical line and inside the critical strip into the open right half-strip. The standard nonvanishing theorem excludes real part at least one.

For nonpositive real part, the same functional equation and the nonvanishing of the gamma and exponential factors force a trivial zeta zero. This is a pure Mathlib reduction with no golden structure; it does not assert either premise or the Riemann hypothesis unconditionally.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh`
