# Averaged gain reconstruction on chordal graphs

## Abstract

Averaging over the predecessors gives a uniform error bound depending on the clique number.

**Theorem 1.1 (The clique-bounded reconstruction estimate).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow ((\forall s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{toSet}\left(s\right)\right)) \Rightarrow (\operatorname{card}\left(s\right) \le k+1)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (4-\frac{4}{\operatorname{real}\left(k\right)}) \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential.exists_clique_bounded_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the statement, toSet takes the underlying set of a finite set, real casts a natural number to a real, and norm is the seminorm on E.

Choose a root in each connected component and partition its vertices into distance layers. For a component of the subgraph at or above a fixed layer, its shadow is the clique of its neighbors in the preceding layer. Above the first layer, a common predecessor of the entire shadow extends it by one vertex to a clique. Thus every predecessor set has at most k vertices. In the first layer the predecessor set is the root alone.

Transport the potential along the chain of common predecessors used as anchors. At each vertex add the mean of the gains along the two-edge paths from its anchor through its predecessors. The root has potential zero and the first-layer edges from the root have zero residual.

Across consecutive layers, compare through the later component's anchor. On each side, one predecessor gives the reference path exactly. Each other term uses at most two triangle comparisons. The norm of each mean difference is therefore at most two times the triangle tolerance times one minus the reciprocal of the predecessor count. Adding both bounds gives the stated coefficient.

For adjacent vertices in the same layer, chordality orders their predecessor sets by inclusion. Fix a predecessor from the smaller set and average against the larger set. The matching predecessor costs one triangle comparison, and each distinct predecessor costs at most three. Averaging over the smaller set preserves the bound of three minus two divided by k, which is at most the stated coefficient for k at least two.

Each connected component has its own potential. The coefficient is eight thirds for k equal to three and three for k equal to four.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential.exists_clique_bounded_banach_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential](UniformGainPotential.md)
