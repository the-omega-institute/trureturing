# Finite Deficiency Triangle

## Abstract

One-way finite experiment deficiency satisfies the triangle inequality under simulator composition.

**Theorem 1.1 (Finite deficiency obeys the triangle inequality).**

$$\begin{gathered}\forall Theta, X, Y, Z: Type,\\{}\operatorname{Fintype}(Theta) \land \operatorname{Nonempty}(Theta) \land \operatorname{Fintype}(X) \land \operatorname{Fintype}(Y) \land \operatorname{Fintype}(Z),\\{}E: \operatorname{FiniteMarkovKernel}(Theta, X), F: \operatorname{FiniteMarkovKernel}(Theta, Y), G: \operatorname{FiniteMarkovKernel}(Theta, Z) \Rightarrow\\{}\operatorname{finiteDeficiency}(G, E) \leq \operatorname{finiteDeficiency}(G, F) + \operatorname{finiteDeficiency}(F, E).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyTriangle.finite_deficiency_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two row-stochastic simulators compose to a row-stochastic simulator. The total-variation triangle inequality and channel contraction bound its error, and independent infima give the stated deficiency inequality.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyTriangle.finite_deficiency_triangle`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](FiniteDeficiencyRiskTransfer.md)
