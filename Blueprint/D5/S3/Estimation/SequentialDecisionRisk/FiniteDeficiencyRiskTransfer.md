# Finite Deficiency Risk Transfer

## Abstract

One-way finite experiment deficiency bounds the increase in optimal risk for every loss in the unit interval.

**Theorem 1.1 (Deficiency controls bounded-loss Bayes risk).**

$$\begin{gathered}\forall Theta, X, Y, A: Type,\\{}\operatorname{Fintype}(Theta) \land \operatorname{Nonempty}(Theta) \land \operatorname{Fintype}(X) \land \operatorname{Fintype}(Y) \land \operatorname{Fintype}(A),\\{}pi: Theta \to \mathbb{R}, ell: Theta \to A \to \mathbb{R}, E: Theta \to X \to \mathbb{R}, F: Theta \to Y \to \mathbb{R},\\{}(\forall theta, 0 \leq \operatorname{apply}(pi, theta)) \land \operatorname{sum}(pi) = 1 \land \operatorname{IsRowStochastic}(E) \land \operatorname{IsRowStochastic}(F),\\{}(\forall theta, a, 0 \leq \operatorname{apply}(ell, theta, a) \land \operatorname{apply}(ell, theta, a) \leq 1) \Rightarrow\\{}\operatorname{finiteBayesRisk}(pi, ell, E) \leq \operatorname{finiteBayesRisk}(pi, ell, F) + \operatorname{finiteDeficiency}(F, E).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.deficiency_risk_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target decision is transported through each source-to-target simulator. The frozen statewise total-variation bound is averaged by the prior, after which extended-nonnegative infima optimize the decision and simulator independently.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.deficiency_risk_bound`
- Dependency: [D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport](../DecisionRisk/BoundedRiskSimulatorTransport.md)
