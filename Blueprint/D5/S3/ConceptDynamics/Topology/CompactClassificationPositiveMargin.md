# Compact Classification Positive Margin

## Abstract

A compact continuous discrete classifier has a positive attained class margin, while intersecting distinct fiber closures obstruct continuity.

**Theorem 1.1 (Cross-class distance has a positive attained minimum).**

$$\begin{gathered}\forall X, Y: \operatorname{Type},\\{}(\operatorname{MetricSpace}(X) \land \operatorname{CompactSpace}(X) \land \operatorname{TopologicalSpace}(Y) \land \operatorname{DiscreteTopology}(Y)) \Rightarrow\\{}\forall T: X \to Y,\\{}((\operatorname{Continuous}(T) \land \exists x, xPrime: X, T(x) \neq T(xPrime)) \Rightarrow \operatorname{let} P: \operatorname{Set}(\operatorname{Product}(X, X)) := \{p: \operatorname{Product}(X, X) | T(\operatorname{fst}(p)) \neq T(\operatorname{snd}(p))\},D: \operatorname{Set}(\mathbb{R}) := \{\operatorname{dist}(\operatorname{fst}(p), \operatorname{snd}(p)) | p\in P\},delta: \mathbb{R} := \operatorname{sInf} D\operatorname{in} (0 < delta \land delta\in D \land \forall x, xPrime: X, \operatorname{dist}(x, xPrime) < delta \Rightarrow T(x) = T(xPrime))) \land\\{}((\exists y, z: Y, y \neq z \land \operatorname{Nonempty}(\operatorname{inter}(\operatorname{closure}(\operatorname{preimage}(T, \{y\})), \operatorname{closure}(\operatorname{preimage}(T, \{z\}))))) \Rightarrow \neg \operatorname{Continuous}(T)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CompactClassificationPositiveMargin.compact_classification_positive_margin_and_closure_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public construction first selects pairs whose classifier values differ, then maps those pairs to their metric distances, and finally takes the infimum of that distance image. Compactness and discreteness make the pair set compact, so its distance image is compact and the infimum is attained.

The nonconstant premise supplies a cross-class pair. At an attained minimum, the two points remain distinct, hence the margin is positive. Any closer pair with different labels would contradict minimality.

The obstruction clause has its own premise and does not assume continuity. Under continuity, discrete singleton fibers are closed, so a point in both closures would receive two distinct labels.

The source's displayed minimum has an empty index set for a constant classifier. The positive-margin implication therefore states nonconstancy explicitly; the closure obstruction remains unconditional.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/CompactClassificationPositiveMargin.compact_classification_positive_margin_and_closure_obstruction`
