# Posterior History Compression

## Abstract

The posterior measure compresses history for prediction and continuation decisions.

**Theorem 1.1 (The posterior determines every future decision quantity).**

$$\begin{gathered}\forall X, H, I, E, P, A: Type,\\{}\operatorname{MeasurableSpace}\left(X\right),\\{}pi: H \to \operatorname{Measure}\left(X\right),\\{}Q: I \to E \to X \to ENNReal,\\{}C: P \to X \to ENNReal,\\{}L: A \to X \to ENNReal,\\{}h, h': H, pi(h) = pi(h') \Rightarrow\\{}(\forall i: I, e: E, \operatorname{lintegral}\left(x, Q(i)(e)(x), pi(h)\right) = \operatorname{lintegral}\left(x, Q(i)(e)(x), pi(h')\right))\\{}\land\\{}\operatorname{inf}\left(a, \operatorname{lintegral}\left(x, L(a)(x), pi(h)\right)\right) = \operatorname{inf}\left(a, \operatorname{lintegral}\left(x, L(a)(x), pi(h')\right)\right)\\{}\land\\{}(\forall p: P, \operatorname{lintegral}\left(x, C(p)(x), pi(h)\right) = \operatorname{lintegral}\left(x, C(p)(x), pi(h')\right))\\{}\land\\{}\operatorname{inf}\left(p, \operatorname{lintegral}\left(x, C(p)(x), pi(h)\right)\right) = \operatorname{inf}\left(p, \operatorname{lintegral}\left(x, C(p)(x), pi(h')\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/PosteriorHistoryCompression.posterior_history_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Histories are mapped to posterior measures on an arbitrary measurable hidden-state carrier. Future event probabilities depend on a hidden state and selected experiment, never directly on history.

A loss family constructs Bayes risk by taking the infimum of posterior expected losses. A continuation policy likewise has a posterior expected cost, and the optimal continuation value is the infimum over all such policies.

The four displayed conclusions separately expose prediction, Bayes risk, every policy cost, and optimal continuation value. Equality of the posterior measures identifies each construction.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/PosteriorHistoryCompression.posterior_history_compression`
