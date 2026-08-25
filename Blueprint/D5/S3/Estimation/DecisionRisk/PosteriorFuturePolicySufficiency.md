# Posterior Future-Policy Sufficiency

## Abstract

Equal posteriors give equal conditional Bayes values for every future policy.

**Theorem 1.1 (The posterior is universally sufficient for future-policy Bayes value).**

$$\begin{gathered}\forall Theta, H, P, F,\\{}\operatorname{Fintype}(Theta),\\{}joint: Theta \to H \to NNReal,\\{}Q: P \to Theta \to \operatorname{PMF}(F),\\{}h, hPrime: H,\\{}\operatorname{posterior}(joint, h) = \operatorname{posterior}(joint, hPrime) \Rightarrow\\{}\forall policy: P, A: \operatorname{Type},\\{}ell: Theta \to A \to ENNReal,\\{}\operatorname{inf}(d, \operatorname{sum}(theta, \operatorname{posterior}(joint, h)(theta) \cdot \operatorname{tsum}(f, Q(policy)(theta)(f) \cdot ell(theta)(d(f))))) = \operatorname{inf}(d, \operatorname{sum}(theta, \operatorname{posterior}(joint, hPrime)(theta) \cdot \operatorname{tsum}(f, Q(policy)(theta)(f) \cdot ell(theta)(d(f))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency.posterior_future_policy_universal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite hidden-state joint weight constructs the canonical posterior of each history. The future experiment semantics are supplied as a policy-indexed family of state-conditioned PMFs on an arbitrary complete future-transcript carrier.

For a fixed future policy, a terminal decision may depend on the entire future transcript. Its conditional risk mixes the supplied loss over the current posterior and that policy's transcript law; the conditional Bayes value is the infimum over all such decisions.

The theorem quantifies every policy, action carrier, and nonnegative extended-real loss publicly. Replacing one history by another with the same posterior leaves the complete displayed value unchanged.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency.posterior_future_policy_universal_sufficiency`
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency](PosteriorUniversalSufficiency.md)
