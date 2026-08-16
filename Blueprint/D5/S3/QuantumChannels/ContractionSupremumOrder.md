# Amplitude-Damping Contraction Suprema Are Ordered

## Abstract

The pointwise SLD-KM-RLD amplitude-damping order lifts to the corresponding positive open-axis suprema of the scalar contraction-ratio model.

**Theorem 1.1 (The positive-axis contraction-ratio suprema are ordered).**

$$0\le\Gamma < 1 \Rightarrow \operatorname{sup}_{0 < u < 1} eta_{SLD}(\Gamma,u) \le \operatorname{sup}_{0 < u < 1} eta_{KM}(\Gamma,u) \le \operatorname{sup}_{0 < u < 1} eta_{RLD}(\Gamma,u)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionSupremumOrder.contraction_supremum_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a damping parameter gamma in the interval from zero inclusive to one exclusive. Taking the supremum over the positive open Bloch axis preserves the imported pointwise ordering of the SLD, KM, and RLD coherence ratios. Boundedness follows from the imported RLD endpoint bound, while the two supremum comparisons use monotonicity of the indexed supremum.

This theorem closes the sup-level omission recorded by the producer at ContractionSpectrumOrder.lean:139-142: it lifts the scalar positive-axis pointwise order to the corresponding iSup order. It does NOT close the producer's recorded contraction-coefficient gap. The all-state reduction remains open and is NOT discharged by this wave: there is no all-state coefficient definition or reduction from all input states to the positive scalar axis. No claim is made about the negative axis.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionSupremumOrder.contraction_supremum_order`
- Dependency: [D5/S3/QuantumChannels/ContractionSpectrumOrder](ContractionSpectrumOrder.md)
