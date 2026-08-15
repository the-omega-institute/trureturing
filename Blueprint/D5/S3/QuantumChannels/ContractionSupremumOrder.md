# Amplitude-Damping Contraction Suprema Are Ordered

## Abstract

The pointwise SLD-KM-RLD amplitude-damping order lifts to the corresponding positive open-axis suprema of the scalar contraction-ratio model.

**Theorem 1.1 (The positive-axis contraction-ratio suprema are ordered).**

$$0\le\Gamma < 1 \Rightarrow \operatorname{sup}_{0 < u < 1} eta_{SLD}(\Gamma,u) \le \operatorname{sup}_{0 < u < 1} eta_{KM}(\Gamma,u) \le \operatorname{sup}_{0 < u < 1} eta_{RLD}(\Gamma,u)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionSupremumOrder.contraction_supremum_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a damping parameter gamma in the interval from zero inclusive to one exclusive. Taking the supremum over the positive open Bloch axis preserves the imported pointwise ordering of the SLD, KM, and RLD coherence ratios. Boundedness follows from the imported RLD endpoint bound, while the two supremum comparisons use monotonicity of the indexed supremum.

This theorem orders suprema of the repository's scalar coherenceRatio model only for u in the open interval from zero to one. It does not establish an all-state reduction and makes no claim about the negative axis.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionSupremumOrder.contraction_supremum_order`
- Dependency: [D5/S3/QuantumChannels/ContractionSpectrumOrder](ContractionSpectrumOrder.md)
