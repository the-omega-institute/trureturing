# Belief Markov Update

## Abstract

Finite predictive output weights are the observed marginal, and conditioning the same joint weight gives the canonical totalized Bayes update.

**Theorem 1.1 (The observed marginal is the predictive output law).**

$$\begin{gathered}\forall \theta, Y: Type,\\{}\operatorname{Fintype}(\theta), L: \theta \to Y \to NNReal,\\{}pi: \theta \to NNReal,\\{}(y) \mapsto \operatorname{historyMass}((x, y) \mapsto pi(x) \times L(x, y), y) = \operatorname{predictiveOutputLaw}(L, pi).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.output_marginal_follows_predictive_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mix the state-conditioned likelihood against the current finite belief. Marginalizing the corresponding hidden-state and output weight over the hidden state gives exactly that named predictive law.

**Theorem 1.2 (The actual next belief is the canonical posterior update).**

$$\begin{gathered}\forall \theta, Y: Type,\\{}\operatorname{Fintype}(\theta), L: \theta \to Y \to NNReal,\\{}pi: \theta \to NNReal, y: Y,\\{}\operatorname{posterior}((x, y) \mapsto pi(x) \times L(x, y), y) = \operatorname{posteriorUpdate}(L, pi, y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.actual_next_belief_eq_posterior_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditioning the same hidden-state and output weight at an observed output has the numerator and normalizer of the existing posteriorUpdate. Thus the history-side next belief and belief-side update coincide.

**Lemma 1.3 (A predictive-null output receives the zero posterior).**

$$\begin{gathered}\forall \theta, Y: Type,\\{}\operatorname{Fintype}(\theta), L: \theta \to Y \to NNReal,\\{}pi: \theta \to NNReal, y: Y,\\{}\operatorname{predictiveOutputLaw}(L, pi)(y) = 0 \Rightarrow\\{}\operatorname{posteriorUpdate}(L, pi, y) = (x) \mapsto 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.zero_predictive_mass_update_is_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source allows any conditional version on a predictive-null output. The repository chooses a concrete version: NNReal division by zero returns zero, so every coordinate of the updated belief is zero.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.actual_next_belief_eq_posterior_update`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.output_marginal_follows_predictive_law`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.zero_predictive_mass_update_is_zero`
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency](../DecisionRisk/PosteriorUniversalSufficiency.md)
