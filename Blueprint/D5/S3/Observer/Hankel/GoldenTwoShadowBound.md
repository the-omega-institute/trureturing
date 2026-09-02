# Golden Two-Shadow Bound

## Abstract

A contractive continuous linear map satisfies one six-entry golden Gram equivalence, and the spectral threshold is sharp.

**Theorem 1.1 (Six golden Gram criteria agree at the maximal threshold).**

$$\begin{aligned}\forall V, W: \operatorname{Type}(),\\{}[\operatorname{NormedAddCommGroup}(V)] \land [\operatorname{InnerProductSpace}(\mathbb{C}, V)] \land [\operatorname{CompleteSpace}(V)],\\{}[\operatorname{NormedAddCommGroup}(W)] \land [\operatorname{InnerProductSpace}(\mathbb{C}, W)] \land [\operatorname{CompleteSpace}(W)],\\{}(\forall H: \operatorname{ContinuousLinearMap}(\mathbb{C}, V, W), \left\lVert H \right\rVert \leq 1 \Rightarrow\\{}let D: \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V) = H^{*} \circ H;\\{}\operatorname{List.TFAE}([D^{2} \le I - D, D + D^{2} \le I, \left\lVert D \right\rVert \le \phi^{-1}, \left\lVert H \right\rVert \le \sqrt{\phi^{-1}}, \exists C: \operatorname{Units}(\operatorname{ContinuousLinearMap}(\mathbb{C}, V, V)), \operatorname{val}(C) = I - D \land \operatorname{val}(C^{-1}) \le \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V), \phi^{2}), \exists C: \operatorname{Units}(\operatorname{ContinuousLinearMap}(\mathbb{C}, V, V)), \operatorname{val}(C) = I - D \land D \cdot \operatorname{val}(C^{-1}) \le \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, V, V), \phi)])) \land (\\{}\operatorname{Nontrivial}(V) \Rightarrow \operatorname{Nontrivial}(W) \Rightarrow\\{}\forall t: \mathbb{R}, \phi^{-1} < t \Rightarrow\\{}\exists H: \operatorname{ContinuousLinearMap}(\mathbb{C}, V, W), \left\lVert H \right\rVert \le 1 \land \left\lVert {H^{*} \circ H} \right\rVert \le t\\{}\land \neg ({H^{*} \circ H}^{2} \le I - {H^{*} \circ H})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/GoldenTwoShadowBound.golden_two_shadow_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every contractive continuous linear map, the positive operator D is constructed as its adjoint composed with the map. The six displayed formulas are entries of one List.TFAE statement.

The inverse criteria quantify units whose values are exactly I-D, so the display records invertibility together with each order bound.

When both Hilbert spaces are nontrivial, every spectral threshold strictly above the inverse golden ratio admits a contractive rank-one map with Gram norm below that threshold for which the positive two-shadow inequality fails. Thus the golden threshold is maximal.

## References

- Truth anchor: `D5/S3/Observer/Hankel/GoldenTwoShadowBound.golden_two_shadow_bound`
