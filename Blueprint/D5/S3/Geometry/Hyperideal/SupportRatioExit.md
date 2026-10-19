# Finite support ratio exit

## Abstract

A finite family of affine-linear supports admits a maximal-ratio exit point.

Let S be a finite index set and let each L_r be affine-linear along the ray from a to x. Assume every support in S is strictly negative at a, supports outside S vanish at a, and all supports are nonpositive at x. If at least one support increases strictly from a to x, choose a maximal increase ratio. The resulting t is positive and at most one; the rescaled point remains in every support halfspace and lies on a supporting trace.

**Theorem 1.1 (A maximal support ratio reaches a boundary).**

$$\forall r \in S\left(\right), L\left(r, a\right) < 0 \Rightarrow ratioExit\left(S, L, a, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SupportRatioExit.support_ratio_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is a finite-dimensional ratio-maximization lemma. It supplies a reusable exit construction for polytope and support-ray arguments; no particular geometric body or subdivision is assumed.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SupportRatioExit.support_ratio_exit`
