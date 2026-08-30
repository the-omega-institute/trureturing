# Chebyshev Signed-Distance Separator

## Abstract

First Chebyshev slack separates nonnegative and negative squared distances.

**Theorem 1.1 (First Chebyshev Slack Separates Signed Squared Distance).**

$$\forall a, x, \delta: \mathbb{R},\\{}(\frac{1}{4} < a) \land (0 \leq x) \land (0 < \delta) \land (\delta^{2} < a) \Rightarrow\\{}\operatorname{let} u_{on} = \frac{x - a}{x + a},\\{}\operatorname{let} s_{on} = 1 - T_{1}(u_{on})^{2},\\{}\operatorname{let} u_{off} = \frac{-\delta^{2} - a}{-\delta^{2} + a},\\{}\operatorname{let} s_{off} = 1 - T_{1}(u_{off})^{2},\\{}((u_{on} \in [-1, 1]) \land\\{}(s_{on} \in [0, 1]) \land\\{}(u_{off} < -1) \land\\{}(s_{off} < 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator.first_chebyshev_slack_separates_signed_squared_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above the stated scale thresholds, a nonnegative squared-distance input has compact coordinate in the closed unit interval and first Chebyshev slack in the interval from zero to one. The negative signed value has coordinate below negative one and strictly negative slack.

This is only a finite algebraic separator under the four explicit hypotheses. It makes no converse claim and does not claim that a xi spectrum supplies the signed-distance observation.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator.first_chebyshev_slack_separates_signed_squared_distance`
- Dependency: [D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity](ChebyshevSlackPositivity.md)
