# Finite Power Extrapolation Risk

## Abstract

Matching finite-horizon prediction bounds for strictly stable scalar powers.

**Definition 1.1 (Risk at a fixed horizon).**

Lean statement: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.risk`

*Formalization.* `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.risk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stable scalar parameter a lies strictly between zero and one and produces the response a to the power k. The observations from time zero through T differ from these responses by at most eta at every coordinate. An estimator is any function from this real observation vector to a real prediction. Its risk at horizon H is the supremum of absolute error over all such parameters and compatible data. Extended nonnegative real values include estimators with infinite worst-case loss.

**Definition 1.2 (Optimal worst-case risk).**

Lean statement: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.minimaxRisk`

*Formalization.* `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.minimaxRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minimax risk is the infimum of the fixed-horizon risks over every deterministic scalar estimator. There are no restrictions on computation, measurability, or the range of an estimator. The observation error is a deterministic coordinatewise bound, not a noise variance.

**Definition 1.3 (Endpoint power prediction).**

Lean statement: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.endpointEstimator`

*Formalization.* `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.endpointEstimator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Clamp the observation at time T to the interval from zero to one, obtaining z, and predict z to the real power H/T. For positive T and H at least T, this power map has Lipschitz constant at most H/T on the unit interval.

**Theorem 1.4 (Matching bounds at every finite horizon).**

Lean statement: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.finite_power_extrapolation_risk`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.finite_power_extrapolation_risk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers 1 <= T <= H and all positive eta, the minimax risk is at least min(eta H/(2T), 1/16) and at most min(1/2, eta H/T). In particular it lies between (1/16) min(1, eta H/T) and min(1, eta H/T). These comparison constants are uniform in all three parameters.

Set d = min(2 eta/T, 1/(4H)), a = 1-d, and b = 1-2d. Both parameters are strictly stable. Their powers differ by at most 2 eta throughout the observation window, so the coordinatewise midpoint is compatible with both. Bernoulli's inequality and the mean value theorem give separation at least Hd/2 at horizon H. Every prediction on this common data has error at least Hd/4 on one of the two parameters. This yields the stated lower bound even for estimators with infinite risk.

Clamping does not increase the endpoint observation error. The endpoint power predictor therefore has error at most eta H/T. The constant prediction one half has error at most one half, giving the other upper bound. All responses have one-dimensional strictly stable realizations; their nonempty Hankel sections are positive semidefinite of rank one.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.endpointEstimator`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.finite_power_extrapolation_risk`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.minimaxRisk`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk.risk`
- Dependency: [D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk](../../Observer/Hankel/RankOneInfiniteHorizonRisk.md)
