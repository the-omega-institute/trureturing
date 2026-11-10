# Finite Bayes-Risk Dominance Criterion

## Abstract

Exact randomized postprocessing between finite experiments is equivalent to real Bayes-risk dominance for every finite decision problem.

**Theorem 1.1 (Decision dominance characterizes finite postprocessing).**

$$\begin{gathered}\forall Theta, X, Y: Type,\\{}\operatorname{Fintype}(Theta) \land \operatorname{Nonempty}(Theta) \land \operatorname{Fintype}(X) \land \operatorname{Fintype}(Y),\\{}E: Theta \to X \to \mathbb{R}, F: Theta \to Y \to \mathbb{R},\\{}\operatorname{IsRowStochastic}(E) \land \operatorname{IsRowStochastic}(F) \Rightarrow\\{}{(\exists K: \operatorname{FiniteMarkovKernel}(X, Y), F = (theta \mapsto \operatorname{channelOutput}(K, E(theta)))) \Leftrightarrow\\{}(\forall A: Type, \operatorname{Fintype}(A),\\{}pi: Theta \to \mathbb{R}, ell: Theta \to A \to \mathbb{R},\\{}{(\forall theta, 0 \leq pi(theta)) \land \operatorname{sum}(pi) = 1} \Rightarrow\\{}\operatorname{sInf}(\operatorname{range}((d: \operatorname{FiniteMarkovKernel}(X, A) \mapsto \operatorname{finiteBayesCost}(pi, ell, E, d)))) \leq \operatorname{sInf}(\operatorname{range}((d: \operatorname{FiniteMarkovKernel}(Y, A) \mapsto \operatorname{finiteBayesCost}(pi, ell, F, d)))))}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.finite_bayes_risk_dominance_iff_postprocessing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source observation can simulate every target decision whenever a row-stochastic source-to-target kernel reproduces the target experiment. Composing that kernel with a target decision rule gives the corresponding source decision rule at the same real expected cost. The displayed risk is the real infimum of these costs, so negative losses are retained rather than truncated.

Conversely, the finite product of row simplexes is compact and convex. A target outside its simulated image has a strict linear separator; a uniform prior and shifted real loss turn that separator into a finite decision problem that reverses the asserted risk order.

**Lemma 1.2 (Coordinates of a continuous linear functional).**

$$\forall \left(I: \operatorname{Type}\right), \left(\forall \left(J: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{DecidableEq}\left(J\right)] \forall \left(functional: \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), I \to \left(J \to \mathbb{R}\right), \mathbb{R}\right)\right), \left(\forall \left(table: I \to \left(J \to \mathbb{R}\right)\right), \left(functional\left(table\right) = \sum_{i: I} \sum_{j: J} \left(functional\left(\operatorname{Pi.single}\left(i, \operatorname{Pi.single}\left(j, 1\right)\right)\right) \cdot table\left(i, j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.continuous_linear_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite index types I and J with decidable equality, a real continuous linear functional on I → J → ℝ is the sum of its values on the coordinate singletons, weighted by the corresponding table entries. This identity expresses strict separating functionals as finite coefficient tables.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.continuous_linear_expansion`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.finite_bayes_risk_dominance_iff_postprocessing`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../../Divergence/ClassicalDPI.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](DescentDefectBounds.md)
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
