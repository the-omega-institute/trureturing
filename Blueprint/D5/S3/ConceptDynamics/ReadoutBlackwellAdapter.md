# Readout Refinement as Blackwell Garbling

## Abstract

Measurable readout factorization becomes deterministic Blackwell garbling and Bayes-risk monotonicity.

**Theorem 1.1 (Finer measurable readouts have no larger optimal Bayes risk).**

$$\begin{gathered}\forall q_{C}, q_{D}, L, mu: \operatorname{MeasurableRefines}(q_{C}, q_{D}) \Rightarrow\\{}\operatorname{bayesRisk}(L, \operatorname{deterministic}(q_{D}), mu) \leq \operatorname{bayesRisk}(L, \operatorname{deterministic}(q_{C}), mu).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ReadoutBlackwellAdapter.bayesRisk_mono_of_measurable_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Measurable refinement augments the repository factorization preorder with the measurability required to form deterministic kernels.

Mathlib's deterministic-kernel composition identity turns the factor map into a Blackwell garbling from the finer readout to the coarse readout.

The existing repository Blackwell theorem then gives Bayes-risk monotonicity for every prior, measurable decision space, and ENNReal-valued loss.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ReadoutBlackwellAdapter.bayesRisk_mono_of_measurable_refinement`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](ConceptJoinUniversal.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk](../Estimation/DecisionRisk/GarblingIncreasesBayesRisk.md)
