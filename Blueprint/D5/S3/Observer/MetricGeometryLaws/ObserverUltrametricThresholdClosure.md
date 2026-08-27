# Observer Ultrametric Threshold Closure

## Abstract

Supremum distance over a bounded ultrametric readout family is an ultrapseudometric whose nonnegative threshold kernels are equivalence relations.

**Theorem 1.1 (Observer suprema preserve ultrametric threshold closure).**

$$\begin{gathered}\forall P, X, Lambda: \operatorname{Type},\\{}[\operatorname{PseudoMetricSpace}\left(Lambda\right)],\\{}Q: \operatorname{Set}\left(P\right), q: P \to \left(X \to Lambda\right),\\{}\forall a, b: Lambda, \operatorname{dist}\left(a, b\right) \leq 1,\\{}\forall a, b, c: Lambda, \operatorname{dist}\left(a, c\right) \leq \max(\operatorname{dist}\left(a, b\right), \operatorname{dist}\left(b, c\right)) \Rightarrow\\{}\operatorname{let}(d_{Q}: X \to \left(X \to \mathbb{R}\right), \forall x, y: X, d_{Q}(x, y) = \operatorname{sSup}\left(\left\{\operatorname{dist}\left(q\left(p\right)\left(x\right), q\left(p\right)\left(y\right)\right) \mid p \in Q\right\}\right),\\{}K_{Q}: \operatorname{NNReal} \to \left(X \to \left(X \to \operatorname{Prop}\right)\right), \forall epsilon: \operatorname{NNReal}, x, y: X, K_{Q}(epsilon, x, y) \iff d_{Q}(x, y) \leq epsilon)\;\\{}(\forall x, y: X, 0 \leq d_{Q}(x, y)) \land\\{}(\forall x: X, d_{Q}(x, x) = 0) \land\\{}(\forall x, y: X, d_{Q}(x, y) = d_{Q}(y, x)) \land\\{}(\forall x, y, z: X, d_{Q}(x, z) \leq \max(d_{Q}(x, y), d_{Q}(y, z))) \land\\{}\forall epsilon: \operatorname{NNReal}, \operatorname{Equivalence}\left(K_{Q}(epsilon)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/ObserverUltrametricThresholdClosure.observer_ultrametric_threshold_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement constructs d_Q as the real supremum of the coordinate distances over the selected observer set Q. The boundedness premise makes every such supremum well defined.

A coordinate strong triangle inequality passes through the supremum. Self-distance, symmetry, and nonnegativity pass through as well, including the empty observer set where the real supremum is zero.

The threshold carrier is NNReal, so every admitted threshold is nonnegative without an additional premise. Reflexivity, symmetry, and transitivity then follow from the three corresponding distance laws.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/ObserverUltrametricThresholdClosure.observer_ultrametric_threshold_closure`
