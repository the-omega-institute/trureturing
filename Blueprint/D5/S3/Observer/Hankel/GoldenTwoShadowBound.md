# Golden Two-Shadow Bound

## Abstract

A contractive Hankel map satisfies six equivalent golden-ratio Gram bounds.

**Theorem 1.1 (Six golden Gram criteria agree).**

$$\begin{aligned}\forall V, W: \operatorname{Type}(),\\{}[\operatorname{NormedAddCommGroup}(V)] \land [\operatorname{InnerProductSpace}(\mathbb{C}, V)] \land [\operatorname{CompleteSpace}(V)],\\{}[\operatorname{NormedAddCommGroup}(W)] \land [\operatorname{InnerProductSpace}(\mathbb{C}, W)] \land [\operatorname{CompleteSpace}(W)],\\\forall H: \operatorname{ContinuousLinearMap}(\mathbb{C}, V, W), \left\lVert H \right\rVert \leq 1 \Rightarrow\\{}let D: \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V) = H^{*} \circ H;\\{}D^{2} \le I - D \iff D + D^{2} \le I \iff \left\lVert D \right\rVert \le \phi^{-1}\\{}\iff \left\lVert H \right\rVert \le \sqrt{\phi^{-1}} \iff \exists C: \operatorname{Units}(\operatorname{ContinuousLinearMap}(\mathbb{C}, V, V)), \operatorname{val}(C) = I - D \land \operatorname{val}(C^{-1}) \le \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V), \phi^{2})\\{}\iff \exists C: \operatorname{Units}(\operatorname{ContinuousLinearMap}(\mathbb{C}, V, V)), \operatorname{val}(C) = I - D \land D \cdot \operatorname{val}(C^{-1}) \le \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V), \phi).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/GoldenTwoShadowBound.golden_two_shadow_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive operator D is constructed as the adjoint of the Hankel map composed with that map. Contractivity supplies the source positive-contraction scope.

The inverse criteria quantify units whose values are exactly I-D, so the display records invertibility together with each order bound.

## References

- Truth anchor: `D5/S3/Observer/Hankel/GoldenTwoShadowBound.golden_two_shadow_bound`
