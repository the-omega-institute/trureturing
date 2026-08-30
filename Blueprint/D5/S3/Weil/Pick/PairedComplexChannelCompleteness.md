# Paired Complex-Channel Completeness

## Abstract

Strictly positive paired complex-channel energies have the common channel kernel and are definite exactly when the joint observation is injective.

**Theorem 1.1 (Positive paired channels preserve the common kernel).**

$$\forall V: \operatorname{Type}, [\operatorname{AddCommGroup}(V)], [\operatorname{Module}(\mathbb{C}, V)], I: \operatorname{Type}, [\operatorname{Fintype}(I)], m: I \to \operatorname{LinearMap}(V, \mathbb{C}), p: I \to \operatorname{LinearMap}(V, \mathbb{C}), w: I \to \mathbb{R}, \forall i: I, 0 < w(i) \Rightarrow \{x \mid \operatorname{pairedComplexChannelEnergy}(m, p, w, x) = 0\} = \{x \mid \forall i: I, m_{i}(x) = 0 \land p_{i}(x) = 0\} \land (\forall x: V, x \neq 0 \Rightarrow 0 < \operatorname{pairedComplexChannelEnergy}(m, p, w, x)) \iff \operatorname{Injective}(\operatorname{pairedComplexObservation}(m, p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/PairedComplexChannelCompleteness.paired_complex_channel_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The energy is the finite sum of positive sensor weights times the two complex readout norm squares. Therefore zero total energy forces both channels to vanish at every sensor.

The same kernel identity converts strict positivity on every nonzero state into injectivity of the paired observation map, and conversely. No finite-dimensional premise on the state space is required.

## References

- Truth anchor: `D5/S3/Weil/Pick/PairedComplexChannelCompleteness.paired_complex_channel_completeness`
