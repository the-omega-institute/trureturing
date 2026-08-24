# Experiment State and Posterior Decision Separation

## Abstract

The canonical experiment-law quotient is a state-side object, while the target posterior is an evidence-side sufficient input for Bayes decisions.

**Theorem 1.1 (Experiment state and posterior decision separate).**

$$\begin{gathered}\forall X, Law, \theta, E, \operatorname{Finite}\left(\theta\right),\\{}\Lambda: X \to Law, j: \theta \times E \to \mathbb{R}_{\geq 0},\\{}[\operatorname{Injective}\left(\operatorname{kerLift}\left(\Lambda\right)\right) \land \Lambda = \operatorname{kerLift}\left(\Lambda\right) \circ \operatorname{quotientClass}\left(\Lambda\right)] \land\\{}[\forall y, yPrime: E, \operatorname{posterior}\left(j, y\right) = \operatorname{posterior}\left(j, yPrime\right) \Rightarrow\\{}\forall A, \ell: \theta \times A \to \mathbb{R},\\{}\operatorname{conditionalBayesValue}\left(j, y, \ell\right) = \operatorname{conditionalBayesValue}\left(j, yPrime, \ell\right) \land\\{}\operatorname{argmin}\left(\operatorname{conditionalRisk}\left(j, y, \ell\right)\right) = \operatorname{argmin}\left(\operatorname{conditionalRisk}\left(j, yPrime, \ell\right)\right)].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/ExperimentStatePosteriorDecisionSeparation.experiment_state_and_posterior_decision_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complete experiment law is a function from source states to law values. Quotienting the source by equality of those values constructs the canonical experiment state. Mathlib's kernel lift is injective on this quotient and composes with the canonical class map to recover the original law exactly.

On the evidence side, a finite nonnegative joint target-evidence weight constructs the target posterior by normalization. If two evidence values have the same posterior, every fixed real loss family gives the same normalized conditional risk at each action.

Consequently equal posteriors determine both the conditional Bayes value and the full set of Bayes-optimal actions, for every action carrier. The state quotient and posterior are not identified: their public constructions have different source domains, states for the former and evidence for the latter.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/ExperimentStatePosteriorDecisionSeparation.experiment_state_and_posterior_decision_separation`
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency](PosteriorUniversalSufficiency.md)
