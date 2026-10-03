# Uniform Lower Quantile Series

## Abstract

A finite measure and arbitrarily reliable uniform lower quantiles force a nonnegative series to diverge almost everywhere, without independence.

**Theorem 1.1 (Almost-everywhere divergence from marginal lower quantiles).**

$$\operatorname{FiniteMeasure}\left(\mu\right) \land (\forall j, \operatorname{Measurable}\left(X_{j}\right)) \land \sum_{j} w_{j}=\infty \land (\forall \Delta>0, \exists c>0, \forall j, \mu(\operatorname{set}\left(x, X_{j}(x)<c w_{j}\right))\leq\Delta) \Rightarrow \mu(\operatorname{set}\left(x, \sum_{j} X_{j}(x)\neq\infty\right))=0$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries.ae_tsum_eq_top_of_uniform_lower_quantiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weights and measurable variables are nonnegative extended real numbers. Error and scale are finite positive real numbers. For each error one scale works for every index, rather than a different scale for each index.

Restricting to a positive-measure event with bounded total determines the error as half its measure. Every restricted summand then has a uniform integral lower bound. Tonelli's theorem contradicts the finite integral of the bounded total.

For an absolute discrepancy with uniform quadratic-scale marginal tightness, the reciprocal square-root logarithmic profile has these lower quantiles against the divergent weights one divided by (j+1) log(j+2). A predictable hazard bounded below by that profile consequently has almost-sure accumulated divergence.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries.ae_tsum_eq_top_of_uniform_lower_quantiles`
