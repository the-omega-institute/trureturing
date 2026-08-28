# Causal Posterior Sufficiency

## Abstract

A finite causal posterior determines future predictions and Bayes decisions.

**Theorem 1.1 (The causal posterior determines prediction and decision).**

$$\begin{gathered}\forall M, H, I, Y: Type,\\{}\operatorname{Fintype}(M), w: M \to H \to NNReal,\\{}L: I \to M \to \operatorname{PMF}(Y),\\{}h, h': H, \operatorname{posterior}(w, h) = \operatorname{posterior}(w, h') \Rightarrow\\{}(\forall i: I, y: Y, \operatorname{sum}(m, \operatorname{posterior}(w, h)(m) \times L(i)(m)(y)) = \operatorname{sum}(m, \operatorname{posterior}(w, h')(m) \times L(i)(m)(y)))\\{}\land\\{}(\forall i: I, A: Type, ell: M \to A \to ENNReal, \operatorname{setOf}(d, \forall d': Y \to A, \operatorname{sum}(m, \operatorname{posterior}(w, h)(m) \times \operatorname{tsum}(y, L(i)(m)(y) \times ell(m)(d(y)))) \leq \operatorname{sum}(m, \operatorname{posterior}(w, h)(m) \times \operatorname{tsum}(y, L(i)(m)(y) \times ell(m)(d'(y))))) = \operatorname{setOf}(d, \forall d': Y \to A, \operatorname{sum}(m, \operatorname{posterior}(w, h')(m) \times \operatorname{tsum}(y, L(i)(m)(y) \times ell(m)(d(y)))) \leq \operatorname{sum}(m, \operatorname{posterior}(w, h')(m) \times \operatorname{tsum}(y, L(i)(m)(y) \times ell(m)(d'(y)))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/CausalPosteriorSufficiency.causal_posterior_determines_predictions_and_bayes_decisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model carrier is finite and histories induce the canonical normalized posterior from their joint weights. A future law is indexed only by the selected intervention and true model, so it contains no direct history argument.

The first displayed conclusion constructs every future-output predictive mass by mixing that model-conditioned law against the current posterior. Thus every intervention and output is covered publicly.

The second conclusion constructs posterior expected loss for every output-dependent decision rule and equates the full sets of minimizers. This states Bayes-decision sufficiency directly, rather than exposing only an optimal value.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/CausalPosteriorSufficiency.causal_posterior_determines_predictions_and_bayes_decisions`
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency](PosteriorFuturePolicySufficiency.md)
