# Ergodicity of the actual stationary output law

## Abstract

Ergodicity of the actual stationary output law

The shift is the original integer emitted-bit shift, under the same actual joint law and its complete visible marginal.

**Theorem 1.1 (Ergodicity of the actual visible law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity.actual_output_ergodic`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity.actual_output_ergodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual P is ergodic under z(t) mapped to z(1+t). A measurable invariant event admits almost-sure versions from each retained half-line by measurable-cylinder approximation, stationarity and summable approximation errors. The actual whole-past/future factorization at H0 forces that event to be a Boolean function of H0. Invariance makes this function equal along every positive marked edge, and irreducibility of the original hidden chain makes it constant. This argument uses the actual J throughout and does not infer a pathwise filtration identification from separate-radius stationarity.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity.actual_output_ergodic`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw](PositiveRectangleLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure](TwelveStateFullErasure.md)
