# Posterior Stopping MAP Error Bound

## Abstract

A posterior-maximizing decision made at the stopping threshold has total error at most that threshold.

**Theorem 1.1 (MAP output at the posterior threshold controls total error).**

$$\begin{gathered}\forall X, H,\\{}\operatorname{Finite}(X), \operatorname{DecidableEq}(X),\\{}mu: \operatorname{PMF}(H),\\{}pi: H \to \operatorname{PMF}(X),\\{}xHat: H \to X, epsilon: ENNReal,\\{}(\forall h, x, pi(h)(x) \leq pi(h)(xHat(h))) \land\\{}(\forall h, \exists xStar, (\forall x, pi(h)(x) \leq pi(h)(xStar)) \land 1 - pi(h)(xStar) \leq epsilon) \Rightarrow\\{}\operatorname{tsum}(h, mu(h) \cdot \operatorname{tsum}(x, [xHat(h) \neq x] pi(h)(x))) \leq epsilon.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound.posterior_stopping_map_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stopped-history law is a PMF on an arbitrary history carrier. Each history has a PMF posterior on the finite state space, so their product constructs the stopped joint law directly.

The stopping clause supplies a posterior maximizer with residual mass at most epsilon. The reported state is independently required to maximize the same posterior, hence it has that same residual conditional error.

Summing the conditional error against the normalized history law gives the displayed joint probability of reporting a state different from the true state.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound.posterior_stopping_map_error_bound`
