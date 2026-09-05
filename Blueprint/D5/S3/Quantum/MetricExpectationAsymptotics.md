# Metric Expectation Asymptotics

## Abstract

Abstract incomplete-Gamma endpoint laws imply the stated closed-form asymptotics.

**Theorem 1.1 (Incomplete-Gamma endpoint laws control the closed form).**

$$\forall G \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), g0 \in \operatorname{Real}\left(\right),\; \left(g0 \ne 0 \land \left(\operatorname{positiveOnNonnegative}\left(G\right) \land \left(\operatorname{tendstoAtZeroRight}\left(G, g0\right) \land \operatorname{standardUpperGammaHalfTail}\left(G\right)\right)\right)\right) \Rightarrow \left(\operatorname{tendstoAtZeroRight}\left(\operatorname{normalizedClosedForm}\left(G\right), 1\right) \land \left(\operatorname{tendstoAtZeroRight}\left(\operatorname{normalizedCorrection}\left(G\right), \operatorname{div}\left(\operatorname{div}\left(4, \operatorname{sqrt}\left(2\right)\right), g0\right)\right) \land \operatorname{tendstoAtTop}\left(\operatorname{metricExpectationClosedForm}\left(G\right), 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MetricExpectationAsymptotics.metric_expectation_closed_form_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a positive real function on nonnegative arguments. Assume G tends to a nonzero value g0 at zero from the right and that sqrt(x) exp(x) G(x) tends to one at infinity.

For the source's displayed closed form, the normalized expression tends to one at zero from the right, its first relative correction tends to (4 / sqrt(2)) / g0, and the unnormalized closed form tends to one at infinity.

The atom does not specify the conditional probability law needed to derive the claimed exact expectation. Pinned Mathlib also has no upper incomplete-Gamma API with the required endpoint theorems. The formal statement therefore parameterizes that factor and makes its two standard asymptotic laws explicit; it does not claim the expectation identity itself.

The proof uses Real.tendsto_exp_nhds_zero_nhds_one, Tendsto.inv0, tendsto_pow_atTop, Tendsto.const_mul_atTop, const_div_atTop, and the real square-root identities. Every division is protected by the nonzero endpoint or strict positivity hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/MetricExpectationAsymptotics.metric_expectation_closed_form_asymptotics`
