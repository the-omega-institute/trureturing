# Readout Refinement as Blackwell Garbling

## Abstract

Measurable readout factorization is transported into the existing Blackwell order and Bayes-risk monotonicity.

**Theorem 1.1 (Finer measurable readouts have no larger optimal Bayes risk).**

Lean statement: `D5/S3/ConceptDynamics/ReadoutBlackwellAdapter.bayesRisk_mono_of_measurable_refinement`

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
