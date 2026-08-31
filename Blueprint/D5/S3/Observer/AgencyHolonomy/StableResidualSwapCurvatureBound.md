# Stable Residual Swap Curvature Bound

## Abstract

Stable swap curvature is linear-quadratic in residual local factors.

**Definition 1.1 (Stable residual swap curvature).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.stableResidualSwapCurvature`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.stableResidualSwapCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write the two scalar local factors as one plus their residuals and their stable-channel memory injections as residual times channel. This definition is the adjacent-swap defect of those two lifted updates.

**Theorem 1.2 (Residual factors control stable swap curvature).**

$$\begin{gathered}\forall K: NormedField, a, r_{p}, r_{q}, v_{p}, v_{q}: K,\\{}(\left\lVert v_{p} \right\rVert \leq 1 \land \left\lVert v_{q} \right\rVert \leq 1) \Rightarrow\\{}C_{st}(a, r_{p}, r_{q}, v_{p}, v_{q}) = (a - 1) \cdot (r_{p} \cdot v_{p} - r_{q} \cdot v_{q}) + r_{p} \cdot r_{q} \cdot (v_{q} - v_{p}) \land\\{}\left\lVert C_{st}(a, r_{p}, r_{q}, v_{p}, v_{q}) \right\rVert \leq \left\lVert (a - 1) \right\rVert \cdot (\left\lVert r_{p} \right\rVert + \left\lVert r_{q} \right\rVert) + 2 \cdot \left\lVert r_{p} \right\rVert \cdot \left\lVert r_{q} \right\rVert \land\\{}(\forall \varepsilon: \mathbb{R}, (0 \leq \varepsilon \land \left\lVert r_{p} \right\rVert \leq \varepsilon \land \left\lVert r_{q} \right\rVert \leq \varepsilon) \Rightarrow \left\lVert C_{st}(a, r_{p}, r_{q}, v_{p}, v_{q}) \right\rVert \leq 2 \cdot \left\lVert (a - 1) \right\rVert \cdot \varepsilon + 2 \cdot \varepsilon^{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.stable_residual_swap_curvature_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any normed field, assume the two channel coordinates have norm at most one. Expanding the adjacent-swap defect gives one term linear in the residuals and one bilinear correction.

The triangle inequality and multiplicativity of the field norm bound the linear term by the sum of the two residual norms and the channel difference by two.

If both residual norms are bounded by a common nonnegative envelope, the defect is at most two times the stable gap times that envelope, plus twice its square. No decay of the envelope is assumed here.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.stableResidualSwapCurvature`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.stable_residual_swap_curvature_bound`
