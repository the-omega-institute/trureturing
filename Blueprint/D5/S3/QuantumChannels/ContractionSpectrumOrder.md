# The Amplitude-Damping Contraction Ratios Are Pointwise Ordered

## Abstract

For amplitude damping on the Bloch axis the three coherence contraction ratios are pointwise ordered SLD below KM below RLD, the key lemma behind the contraction-spectrum ordering.

**Theorem 1.1 (The SLD, KM, and RLD contraction ratios are pointwise ordered).**

$$0\le\Gamma < 1, 0 < u < 1 \Rightarrow eta_{SLD}(\Gamma,u) \le eta_{KM}(\Gamma,u) \le eta_{RLD}(\Gamma,u)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionSpectrumOrder.contraction_spectrum_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a damping parameter gamma in the interval from zero inclusive to one exclusive and an axial Bloch coordinate u in the open unit interval, the three amplitude-damping coherence contraction ratios are pointwise ordered: the SLD ratio is at most the KM ratio, which is at most the RLD ratio. The SLD ratio is the constant one minus gamma; the KM and RLD ratios multiply one minus gamma by the quotient of the respective radial profile (artanh u over u for KM, one over one minus u squared for RLD) at the damped and original coordinates. The profiles are reused verbatim from the frozen AmplitudeDampingContraction module.

The ordering reduces to two monotonicity facts of the artanh radial profile on the open unit interval: artanh u over u is increasing (giving the SLD below KM inequality) and one minus u squared times artanh u over u is decreasing (giving the KM below RLD inequality). Each monotonicity is proved from a locally supplied derivative of artanh — genuine new content, since Mathlib has none — together with the enclosing inequalities u over one plus u squared at most artanh u at most u over one minus u squared, which are reused from the frozen DoubleArtanhBounds module rather than re-proved here.

This records the pointwise contraction-ratio ordering, the key lemma from which the spectrum ordering of the operational contraction coefficients (their suprema over all input states) follows by monotonicity of the supremum; the sup-level statement is not separately formalized, matching the pointwise coherence-ratio framework of AmplitudeDampingContraction.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionSpectrumOrder.contraction_spectrum_order`
- Dependency: [D5/S3/Quantum/DoubleArtanhBounds](../Quantum/DoubleArtanhBounds.md)
- Dependency: [D5/S3/QuantumChannels/AmplitudeDampingContraction](AmplitudeDampingContraction.md)
