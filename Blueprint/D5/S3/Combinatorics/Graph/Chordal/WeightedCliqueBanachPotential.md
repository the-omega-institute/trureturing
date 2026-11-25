# Biased gain reconstruction on chordal graphs

## Abstract

Biased predecessor averaging improves the error coefficient at every finite clique width.

**Theorem 1.1 (The biased predecessor reconstruction estimate).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow ((\forall s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{toSet}\left(s\right)\right)) \Rightarrow (\operatorname{card}\left(s\right) \le k+1)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (4-\frac{4}{\operatorname{real}\left(k\right)}-\frac{2 \cdot (\operatorname{real}\left(k\right)-2)^{2}}{\operatorname{real}\left(k\right) \cdot (\operatorname{real}\left(k\right)-1)^{3}}) \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/WeightedCliqueBanachPotential.exists_biased_clique_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the statement, toSet takes the underlying set of a finite set, real casts a natural number to a real, and norm is the seminorm on E.

Choose a root in each connected component and partition the vertices into distance layers. Each predecessor set is a clique of size at most k, and adjacent vertices at the same layer have nested predecessor sets. Two vertices of a predecessor clique cannot both have k predecessors. Their predecessor sets would coincide, and together with the two vertices would form a clique of size k plus two.

Write delta for (k − 2) divided by k times the square of k − 1. When a predecessor set of size m at least two contains a vertex with k predecessors, give that vertex weight 1/m plus delta and each other vertex weight 1/m minus delta divided by m − 1. Otherwise give every predecessor weight 1/m. These positive weights sum to one and are bounded below by the decreasing function f with f(1) = 1 and f(m) = 1/m − delta/(m − 1) for m at least two.

Transport the potential along the chain of common shadow predecessors used as anchors. At each vertex add the weighted mean of the gains along the two-edge paths from its anchor through its predecessors. The root potential is zero and its incident edges have zero residual.

Across consecutive layers, one predecessor on each side gives the reference path exactly, while each other predecessor costs at most two triangle defects. The sum of the two distinguished weights is at least f(k) plus 1/k plus delta if both predecessor sets have size k, and at least f(k) plus f(k − 1) otherwise. These quantities agree by the definition of delta, giving the displayed bound.

Within a layer, orient an edge so that the first predecessor set is contained in the second. For each predecessor of the first vertex, the matching term of the second weighted mean has error at most one triangle defect and other terms cost at most three. Averaging gives the coefficient 3 − 2 f(k), which is bounded above by the displayed coefficient.

The potentials on the connected components combine to a potential on the graph. For k equal to four the coefficient is 79/27, strictly less than three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/WeightedCliqueBanachPotential.exists_biased_clique_banach_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential](CliqueBoundedBanachPotential.md)
