# Uniform approximation of chordal group gains

## Abstract

Triangle defects give an edge error bound independent of the number of vertices.

Let V be a finite vertex type and H a group with a pseudometric invariant under both left and right multiplication. An oriented edge from i to j carries a label g(i,j). Reversing an edge inverts its label exactly. For each ordered triangle, the distance between g(i,j)g(j,k) and g(i,k) is at most a common nonnegative real number epsilon.

**Theorem 1.1 (A uniform four-defect bound).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall H \in \operatorname{Type}\left(v\right),\; [\operatorname{Finite}\left(V\right)] [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(\operatorname{MulOpposite}\left(H\right), H\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to H\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(j, i\right) = \operatorname{inv}\left(\operatorname{g}\left(i, j\right)\right))) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall k \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, k\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, k\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right) \cdot \operatorname{g}\left(j, k\right), \operatorname{g}\left(i, k\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to H,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right), \operatorname{inv}\left(\operatorname{phi}\left(i\right)\right) \cdot \operatorname{phi}\left(j\right)\right) \le 4 \cdot epsilon)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential.exists_uniform_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two isometric actions express invariance under left and right multiplication. One potential phi gives the claimed error on every oriented edge, with a coefficient independent of the number of vertices.

Choose a root in each connected component and assign vertices their distance from the root. For a component of the subgraph at or above a given layer, its shadow consists of its neighbors in the preceding layer. Two nonadjacent shadow vertices would admit shortest paths through that component and through lower layers. The interiors of these paths are disjoint and have no edges between them. Their union would therefore be a chordless cycle of length at least four.

For every shadow above the root, each vertex in it has a predecessor in the parent shadow. The predecessor sets are linearly ordered by inclusion, since two incomparable sets give a chordless four-cycle. A member of a smallest predecessor set is adjacent to the whole shadow. Use this member as the component anchor, with the root as anchor in the first layer.

Transport along the chain of anchors. To reach a vertex from its component anchor, pass through a chosen predecessor. A cross-layer edge requires at most two triangle comparisons on each side of its shared shadow. For an edge within a layer, the two predecessors coincide or lie in a four-cycle whose chord yields a comparison using at most three triangles. Reversing an edge preserves its error by inversion.

The construction treats each connected component separately and applies to an empty graph. When epsilon is zero, every edge has zero error in the given pseudometric.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential.exists_uniform_approximate_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
