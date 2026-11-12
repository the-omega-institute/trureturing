# Whole-base ball branch of VII98.7

## Abstract

The full-base branch of the original B-only low-affine-dimension argument is
formalized on the original finite-dimensional cone.  An affine coordinate on a
whole-base ball is extended to a linear functional on the entire carrier and
normalized with the original unit, giving a proper effect that separates every
unit antipodal pair.

The segment-face and positive-dimensional-facet branches needed for the complete
VII98.7 statement over arbitrary pure sets require additional arguments.  No finite
pure, PSD, exposedness, smoothness or Z0 assumption is introduced here.

## Theorem

`D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.ball_chart_antipodal_effect`

For the original cone `C`, unit `u`, and an entire `BallChart b`, assume
`pairBase C u p q = base C u`.  For every unit chart direction `n`, there is a
linear map `f : V →ₗ[ℝ] ℝ` with `confirms C u (b.param n) f` and
`f (b.param (-n)) = 0`.  Properness is proved for every point of `C` by
normalizing it into the entire original base.

The consumer
`D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.allAntipodes_of_full_pair_balls`
applies this effect to the original `allAntipodes` predicate when every pair
has a whole-base chart.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.ball_chart_antipodal_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.allAntipodes_of_full_pair_balls`
- Dependency: [WholePairBallConfirmation](WholePairBallConfirmation.md)
