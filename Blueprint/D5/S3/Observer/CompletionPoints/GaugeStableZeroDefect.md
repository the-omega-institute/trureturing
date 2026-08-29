# Gauge Stable Zero Defect

## Abstract

Gauge-invariant normalization and defect data preserve completion status.

**Theorem 1.1 (Gauge transport preserves completion).**

$$\forall normalize: X \to N, target: N, defect: X \to D,\\{}zero: D, gauge: X \to X, x: X,\\{}((\forall x: X, \operatorname{normalize}\left(\operatorname{gauge}\left(x\right)\right) = \operatorname{normalize}\left(x\right)) \land (\forall x: X, \operatorname{defect}\left(\operatorname{gauge}\left(x\right)\right) = \operatorname{defect}\left(x\right))) \Rightarrow (\operatorname{CompletedAt}\left(normalize, target, defect, zero, x\right) \iff \operatorname{CompletedAt}\left(normalize, target, defect, zero, \operatorname{gauge}\left(x\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect.gauge_preserves_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a gauge transformation preserves both normalization and defect values at every state.

For a fixed normalization target, defect zero, and state, the two invariances transport both conjuncts of completion in either direction.

The equivalence is pointwise; invertibility of the gauge map is not assumed.

**Theorem 1.2 (Defect invariance preserves zero defect).**

$$\forall x2 \in \left(\forall x2 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x3 \in \mathord{\cdot},\; \forall x4 \in \left(\forall x4 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \left(\forall x5 \in \mathord{\cdot},\; \mathit{x2}\left(\mathit{x4}\left(\mathit{x5}\right)\right) = \mathit{x2}\left(\mathit{x5}\right)\right) \Rightarrow \left(\forall x6 \in \mathord{\cdot},\; \mathit{x2}\left(\mathit{x6}\right) = \mathit{x3} \Leftrightarrow \mathit{x2}\left(\mathit{x4}\left(\mathit{x6}\right)\right) = \mathit{x3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect.gauge_preserves_zero_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only that the defect value is invariant under the gauge map at every state.

At a fixed state, equality to the designated zero is then equivalent before and after gauge transport.

## References

- Truth anchor: `D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect.gauge_preserves_completion`
- Truth anchor: `D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect.gauge_preserves_zero_defect`
