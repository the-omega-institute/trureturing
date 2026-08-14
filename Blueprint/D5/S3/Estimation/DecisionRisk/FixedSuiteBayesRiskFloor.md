# Fixed-Suite Bayes-Risk Floor

## Abstract

A learner that receives only a fixed finite observation suite cannot beat the suite's Bayes-risk floor by iterating.

**Theorem 1.1 (Every fixed-suite learner remains above the Bayes-risk floor).**

$$\forall m, k\in \mathbb{N},\ \operatorname{Markov}(P_{k}) \Rightarrow \operatorname{bayesRisk}(\ell, T_{m}, \pi) \le \operatorname{avgRisk}(\ell, T_{m}, P_{k}, \pi).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor.fixed_suite_bayes_risk_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation channel T has output type Fin m to X, so every observation is an m-entry suite. The same channel is used at every natural-numbered round. Each P indexed by k is a Markov kernel from that suite to a deployed decision, which models internal randomization without giving the learner a direct input from the hidden task parameter.

Mathlib defines average risk by composing the observation channel with the learner kernel and integrating the loss against the prior. It defines Bayes risk as the infimum of those average risks over all Markov estimators. The displayed inequality is therefore the upstream Bayes-risk lower bound, specialized only enough to retain the fixed suite size and round index.

This closes only the starvation lower-bound clause. The conditional-mode lower bound on unmeasured mass, the fresh-sample comparison with k times m observations, the later qualifications, and the empirical interpretation remain unresolved.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor.fixed_suite_bayes_risk_floor`
