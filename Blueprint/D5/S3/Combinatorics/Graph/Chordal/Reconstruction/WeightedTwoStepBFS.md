# The weighted two-step breadth-first potential

## Abstract

Every weighted two-step breadth-first potential has residual at most four for defect-one gains.

**Theorem 1.1 (A uniform bound for arbitrary predecessor weights).**

$$\forall level \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(level\right),\; [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{Chordal}\left(G\right)) \Rightarrow ((\operatorname{Connected}\left(G\right)) \Rightarrow (\forall r \in V,\; \forall a \in \operatorname{AnchorFamily}\left(G, r\right),\; \forall w \in V \to \left(V \to \mathbb{R}\right),\; \forall g \in V \to \left(V \to \mathbb{R}\right),\; (\operatorname{Anchors}\left(G, r, a\right)) \Rightarrow ((\operatorname{Weights}\left(G, r, w\right)) \Rightarrow ((\operatorname{Flat}\left(G, g\right)) \Rightarrow (\forall u \in V,\; \forall v \in V,\; (\operatorname{Adj}\left(G, u, v\right)) \Rightarrow (\lvert \operatorname{eval}\left(g, u, v\right)-(\operatorname{P}\left(G, r, a, w, g, v\right)-\operatorname{P}\left(G, r, a, w, g, u\right))\rvert  \le 4))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS.two_step_residual_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flat means skew with absolute triangle defect at most one. Anchor choices use the root at depth one and a common predecessor of the shadow in the parent shadow at each later depth. The weights are nonnegative, vanish off the predecessor set, and sum to one at each nonroot vertex.

The potential P transports along successive anchors and adds the weighted mean of the two-edge paths through the predecessors. Root edges have zero residual. Within one layer, both endpoints have the same anchor. The shadow is a clique, and a diagonal in the four-cycle formed by the endpoints and their predecessors yields a comparison using at most three triangles. Across consecutive layers the common transport cancels and four triangle comparisons suffice. Averaging over the predecessor pair preserves the bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS.two_step_residual_bound`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential](../CliqueBoundedBanachPotential.md)
