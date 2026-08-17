# Minimum Mean-Square Hedge

## Abstract

Orthogonal projection gives the unique minimum-mean-square attainable payoff.

**Theorem 1.1 (Orthogonal projection is the unique mean-square hedge).**

$$\forall Y\in M, \Vert\Vert X - Y \Vert\Vert^{2} = \Vert\Vert \operatorname{R}\left(M, X\right) \Vert\Vert^{2} + \Vert\Vert \operatorname{P}\left(M, X\right) - Y \Vert\Vert^{2},\ \operatorname{uniqueMinimizer}(\Vert\Vert X - Y \Vert\Vert^{2}) = \operatorname{P}\left(M, X\right),\ \operatorname{inf}_{Y\in M} \Vert\Vert X - Y \Vert\Vert^{2} = \Vert\Vert \operatorname{R}\left(M, X\right) \Vert\Vert^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/MinimumMeanSquareHedge.minimum_mean_square_hedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be an attainable-payoff subspace of a finite-dimensional real Hilbert space and let X be a target claim. For every Y in M, the squared error splits into the squared orthogonal residual and the squared distance from the projection to Y.

The orthogonal projection of X onto M is characterized by an if-and-only-if as the unique global minimizer over M. The infimum of the squared errors is attained there and equals the squared residual norm.

Pinned Mathlib supplies Submodule.norm_sq_eq_add_norm_sq_starProjection and Submodule.starProjection_minimal as the exact projection cores. Repository searches found no declaration joining all three clauses.

## References

- Truth anchor: `D5/S3/ResourceOrder/MinimumMeanSquareHedge.minimum_mean_square_hedge`
