# Frame Bundle Dimension

## Abstract

A local frame-coordinate space over n coordinates has dimension n+n^2.

**Theorem 1.1 (Local frame coordinates have dimension n plus n squared).**

$$\operatorname{finrank}\left(K, \operatorname{FrameCoordinateSpace}\left(K, n\right)\right) = n + n \cdot n$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/FrameBundleDimension.frame_coordinate_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a field K, a local coordinate description consists of a vector with n coefficients and a frame matrix with n by n coefficients. Their product space therefore has the displayed finite dimension.

Pinned Mathlib was searched before proving. Module.finrank_prod gives the dimension of the product, while Module.finrank_pi_fintype and Module.finrank_fintype_fun_eq_card compute the two function-space dimensions. The Lean proof is a thin normalization wrapper over these library declarations; no packaged theorem for this combined model was found.

This is an honest partial closure of the leading dimension clause only. The canonical fixed-section assertion, the information interpretation, and the later identifications remain unresolved.

## References

- Truth anchor: `D5/S0/Tower/FrameBundleDimension.frame_coordinate_finrank`
