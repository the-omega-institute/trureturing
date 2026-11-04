# Permanent Finite-Prediction Obstruction

## Abstract

A finite autonomous predictor cannot maintain a fixed subunit error forever on an irrational circle rotation.

**Theorem 1.1 (No finite autonomous predictor is permanently accurate).**

$$\forall S, [\operatorname{Fintype} S], \forall G:S\to S, h:S\to \mathbb{C}, s_{0}\in S, x\in \operatorname{AddCircle}(1), alpha, epsilon\in \mathbb{R}, \operatorname{Irrational}(alpha) \land 0<epsilon \land epsilon<\frac{1}{2} (\forall n\in\mathbb{N}, \Vert h(G^{n}(s_{0}))-(x+nalpha)\Vert\leq epsilon) \Rightarrow False.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/PermanentFinitePredictionObstruction.no_permanent_finite_prediction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite state type with an autonomous update G, a complex readout h, and an actual initial state. Fix a phase x on AddCircle 1 and an irrational real increment alpha. If the readout along the finite orbit stayed within epsilon of the rotated phase at every natural time, where 0 < epsilon < 1/2, then the finite-horizon arithmetic bound would hold for every horizon H. Choosing a natural H strictly larger than that fixed bound gives a contradiction. Thus no such finite autonomous predictor can satisfy the subunit error bound forever.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/PermanentFinitePredictionObstruction.no_permanent_finite_prediction`
- Dependency: [D5/S3/Observer/MetricGeometry/ArithmeticHorizon](ArithmeticHorizon.md)
