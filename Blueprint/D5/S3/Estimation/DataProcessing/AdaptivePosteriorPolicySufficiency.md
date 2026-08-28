# Adaptive Posterior-Policy Sufficiency

## Abstract

Equal posteriors generate equal adaptive future laws and recursive Bayes values.

**Theorem 1.1 (The posterior determines adaptive future laws and continuation values).**

$$\begin{gathered}\forall Theta, H, E, Y: \operatorname{Type},\\{}\operatorname{Fintype}(Theta),\\{}j: Theta \to H \to NNReal,\\{}extend: H \to E \to Y \to H,\\{}K: E \to Theta \to \operatorname{PMF}(Y),\\{}\forall h: H, e: E, y: Y,\\{}\operatorname{posterior}(j, extend(h, e, y)) = \operatorname{posteriorUpdate}((theta, o) \mapsto \operatorname{toNNReal}(K(e, theta, o)), \operatorname{posterior}(j, h), y),\\{}h, hPrime: H, \operatorname{posterior}(j, h) = \operatorname{posterior}(j, hPrime) \Rightarrow\\{}\forall policy: \mathbb{N} \to (Theta \to NNReal) \to E,\\{}A: \operatorname{Type}, ell: Theta \to A \to ENNReal, n: \mathbb{N},\\{}\operatorname{adaptiveFutureOutputLaw}(j, extend, K, policy, n, h) = \operatorname{adaptiveFutureOutputLaw}(j, extend, K, policy, n, hPrime) \land\\{}\operatorname{adaptiveContinuationValue}(j, extend, K, policy, ell, n, h) = \operatorname{adaptiveContinuationValue}(j, extend, K, policy, ell, n, hPrime).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency.posterior_adaptive_policy_universal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The experiment kernel is state-conditioned, while the finite-horizon policy selects each next experiment from the current posterior. Observed outputs extend the actual history.

The displayed conditioning premise requires every extended-history posterior to be the canonical Bayes update of the current posterior by the selected experiment kernel.

Induction on the horizon first transports that update through equal posteriors, then identifies both the recursively generated future-output law and the predictive continuation sum.

At horizon zero the continuation value is the infimum of posterior expected loss over the arbitrary action carrier. Thus both conclusions hold for every policy, action type, loss, and finite horizon.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency.posterior_adaptive_policy_universal_sufficiency`
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency](../DecisionRisk/PosteriorUniversalSufficiency.md)
