# Discrete Completion Velocity

## Abstract

The finite-difference completion velocity is a Newton predictor and exactly recovers root displacement for affine layer changes.

**Theorem 1.1 (Completion Layer Difference At Root).**

$$\forall K: Type, F: K \to K, Fnext: K \to K, root: K, [\operatorname{Field}\left(K\right)],\\{}(F root = 0) \Rightarrow\\{}(completionLayerDifference Fnext F root = Fnext root).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.completion_layer_difference_at_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a current root, the layer difference is simply the next layer's residual at that point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Predicted Discrete Velocity At Root).**

$$\forall K: Type, F: K \to K, Fnext: K \to K, dF: K \to K, root: K, [\operatorname{Field}\left(K\right)],\\{}(F root = 0) \Rightarrow\\{}(predictedDiscreteVelocity F Fnext dF root = -Fnext root / dF root).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_at_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root-specialized form of the discrete predictor.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Predicted Discrete Velocity eq Zero iff).**

$$\forall K: Type, F: K \to K, Fnext: K \to K, dF: K \to K, root: K, [\operatorname{Field}\left(K\right)],\\{}(F root = 0) \land (dF root \neq 0) \Rightarrow\\{}(predictedDiscreteVelocity F Fnext dF root = 0 \Leftrightarrow Fnext root = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a regular current root, a zero predictor is equivalent to the next layer also vanishing at the same point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Affine Layer Predicted Velocity).**

$$\forall K: Type, a: K, root: K, delta: K, [\operatorname{Field}\left(K\right)],\\{}(a \neq 0) \Rightarrow\\{}(predictedDiscreteVelocity (\lambda z \mapsto a \times (z - root)) (\lambda z \mapsto a \times (z - (root + delta))) (\lambda value \mapsto a) root = delta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.affine_layer_predicted_velocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact affine layer model: shifting the root by delta produces predicted velocity delta.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Affine Layer Prediction Realized).**

$$\forall K: Type, a: K, root: K, delta: K, [\operatorname{Field}\left(K\right)],\\{}(a \neq 0) \Rightarrow\\{}(\operatorname{let} Fnext: K \to K = \lambda z: K \mapsto a \cdot \left(z - \left(root + delta\right)\right),\\{}\operatorname{let} velocity = \operatorname{predictedDiscreteVelocity}\left(\lambda z: K \mapsto a \cdot \left(z - root\right), Fnext, \lambda z: K \mapsto a, root\right),\\{}\operatorname{Fnext}\left(root + velocity\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.affine_layer_prediction_realized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine prediction agrees with the actual next-layer root.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Predicted Discrete Velocity Scale Invariant).**

$$\forall K: Type, c: K, F: K \to K, Fnext: K \to K, dF: K \to K, s: K, [\operatorname{Field}\left(K\right)],\\{}(c \neq 0) \land (dF s \neq 0) \Rightarrow\\{}(predictedDiscreteVelocity (\lambda z \mapsto c \times F z) (\lambda z \mapsto c \times Fnext z) (\lambda z \mapsto c \times dF z) s = predictedDiscreteVelocity F Fnext dF s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_scale_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Common nonzero rescaling of both layers and the derivative field leaves the prediction unchanged.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.affine_layer_predicted_velocity`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.affine_layer_prediction_realized`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.completion_layer_difference_at_root`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_at_root`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_eq_zero_iff`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.predicted_discrete_velocity_scale_invariant`
- Dependency: [D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField](NewtonCompletionField.md)
