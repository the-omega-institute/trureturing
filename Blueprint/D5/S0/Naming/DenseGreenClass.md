# Dense Properties Meet Every Green Class

## Abstract

Every nonempty open class meets a dense property.

**Proposition 1.1 (A dense property meets every nonempty open class).**

$$\left(\operatorname{Dense}\left(P\right) \land \left(\operatorname{IsOpen}\left(G\right) \land \operatorname{Nonempty}\left(G\right)\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(G, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/DenseGreenClass.dense_inter_green_class_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P and G be subsets of an arbitrary topological space. If P is dense and G is nonempty and open, then G intersects P. Thus an open green class cannot refute the dense property by having empty intersection.

Pinned Mathlib supplies the exact result as Dense.inter_open_nonempty. The Lean declaration is a thin wrapper that preserves the source's intersection orientation.

This is a partial closure of clause (a) only. The safety and liveness decomposition claims, the general property decomposition, and clause (b) on finite observability outside a closed set remain unresolved.

## References

- Truth anchor: `D5/S0/Naming/DenseGreenClass.dense_inter_green_class_nonempty`
