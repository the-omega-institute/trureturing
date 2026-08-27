# Predictive Risk Optimizer Kernel Hierarchy

## Abstract

Complete predictive laws refine expected-risk equivalence, which refines equality of all task optimizer sets.

**Theorem 1.1 (Predictive, risk, and optimizer quotient order).**

$$\begin{gathered}\forall H, Y, L, A: Type,\\{}\operatorname{Fintype}(Y), Psi: H \to \operatorname{PMF}(Y), ell: L \to A \to Y \to \mathbb{R},\\{}\operatorname{ker}(Psi) \subseteq \operatorname{ker}(\operatorname{riskProfile}(Psi, ell)) \land \operatorname{ker}(\operatorname{riskProfile}(Psi, ell)) \subseteq \operatorname{ker}(\operatorname{optimizerProfile}(Psi, ell)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy.predictive_risk_optimizer_kernel_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A history carries a complete probability mass function on finite outcomes. The expected-risk profile is the finite sum of that law against every task, action, and loss coordinate.

The optimizer profile is the complete set of actions attaining the minimum risk for each task. Equality of predictive laws therefore gives equality of risk profiles, and equality of risk profiles gives equality of all optimizer sets.

The theorem uses equality kernels of these source-semantic profiles, so both inclusions remain falsifiable and no quotient carrier is defined by its target relation.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy.predictive_risk_optimizer_kernel_hierarchy`
