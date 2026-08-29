# Finite Bayes-Risk Dominance Criterion

## Abstract

Exact randomized postprocessing between finite experiments is equivalent to Bayes-risk dominance for every finite decision problem.

**Theorem 1.1 (Decision dominance characterizes finite postprocessing).**

$$\begin{gathered}\forall Theta, X, Y: Type,\\{}\operatorname{Fintype}(Theta) \land \operatorname{Nonempty}(Theta) \land \operatorname{Fintype}(X) \land \operatorname{Fintype}(Y),\\{}E: Theta \to X \to \mathbb{R}, F: Theta \to Y \to \mathbb{R},\\{}\operatorname{IsRowStochastic}(E) \land \operatorname{IsRowStochastic}(F) \Rightarrow\\{}(\exists K: \operatorname{FiniteMarkovKernel}(X, Y), F = (theta \mapsto \operatorname{channelOutput}(K, E(theta)))) \Leftrightarrow\\{}(\forall A: Type, \operatorname{Fintype}(A),\\{}pi: Theta \to \mathbb{R}, ell: Theta \to A \to \mathbb{R},\\{}{(\forall theta, 0 \leq pi(theta)) \land \operatorname{sum}(pi) = 1} \Rightarrow\\{}\operatorname{finiteBayesRisk}(pi, ell, E) \leq \operatorname{finiteBayesRisk}(pi, ell, F)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.finite_bayes_risk_dominance_iff_postprocessing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source observation can simulate every target decision whenever a row-stochastic source-to-target kernel reproduces the target experiment. Composing that kernel with a target decision rule gives the corresponding source decision rule at the same cost.

Conversely, the finite product of row simplexes is compact and convex. A target outside its simulated image has a strict linear separator; a uniform prior and shifted real loss turn that separator into a finite decision problem that reverses the asserted risk order.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.finite_bayes_risk_dominance_iff_postprocessing`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
