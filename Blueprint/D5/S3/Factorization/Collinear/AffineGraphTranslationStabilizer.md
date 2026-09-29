# Affine Graph Translation Stabilizer

## Abstract

The translation stabilizer of an affine graph is the slope lift of its abscissa stabilizer.

**Theorem 1.1 (The graph stabilizer is the slope lift).**

$$\operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{Stab}\left(\operatorname{prod}\left(R, R\right), \operatorname{affineGraph}\left(a, b, X\right)\right) = \operatorname{map}\left(\operatorname{Stab}\left(R, X\right), \operatorname{slopeHom}\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Collinear/AffineGraphTranslationStabilizer.affineGraph_stabilizer_eq_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by (h,k) sends the graph over X to the graph over h+X with intercept b+k-ah. Equal graphs have equal first-coordinate projections. Since X is nonempty, equality at one abscissa forces k=ah. This argument works over commutative rings with zero divisors.

## References

- Truth anchor: `D5/S3/Factorization/Collinear/AffineGraphTranslationStabilizer.affineGraph_stabilizer_eq_map`
