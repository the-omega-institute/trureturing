# Simplicial averaging and reconstruction on interval and split graphs

## Abstract

Simplicial averaging gives a finite-size reconstruction bound. Interval and split graphs admit a two-defect bound for bi-invariant pseudometrics.

**Theorem 1.1 (Simplicial averaging).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow ((\forall s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{toSet}\left(s\right)\right)) \Rightarrow (\operatorname{card}\left(s\right) \le k+1)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (\operatorname{real}\left(k\right)-1) \cdot (1-(\frac{\operatorname{real}\left(k\right)-1}{\operatorname{real}\left(k\right)})^{(\operatorname{Natcard}\left(V\right)-1)}) \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.exists_simplicial_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Natcard is the natural-number cardinality of the vertex type, including zero, and the subtraction in the exponent is natural-number subtraction. The function real denotes the natural-to-real cast, toSet denotes the underlying set of a finite set, and norm denotes the seminorm. Delete a simplicial vertex, apply induction to the remaining graph, and extend the potential by the mean of the candidates from its neighbors. A neighborhood has at most k vertices. The difference of any two candidates is bounded by the previous edge radius plus the triangle tolerance. The candidate at the tested edge contributes zero to the sum of differences. Thus the new radius is at most the fraction (k minus one) over k times the old radius plus the triangle tolerance inside the parentheses. Starting with radius zero on a single vertex solves the recurrence to give the displayed finite coefficient. The radius is nondecreasing with vertex count; if a vertex has no neighbors, its assigned value imposes no edge constraint. The coefficient is at most k minus one.

**Theorem 1.2 (Finite interval graphs).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall H \in \operatorname{Type}\left(v\right),\; [\operatorname{Finite}\left(V\right)] [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(\operatorname{MulOpposite}\left(H\right), H\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall l \in V \to \mathbb{R},\; \forall r \in V \to \mathbb{R},\; (\forall i \in V,\; \operatorname{l}\left(i\right) \le \operatorname{r}\left(i\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Leftrightarrow ((i \neq j) \land (\operatorname{max}\left(\operatorname{l}\left(i\right), \operatorname{l}\left(j\right)\right) \le \operatorname{min}\left(\operatorname{r}\left(i\right), \operatorname{r}\left(j\right)\right)))) \Rightarrow (\forall g \in V \to \left(V \to H\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(j, i\right) = \operatorname{inv}\left(\operatorname{g}\left(i, j\right)\right))) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right) \cdot \operatorname{g}\left(j, l\right), \operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow ((\operatorname{IsChordal}\left(G\right)) \land (\exists phi \in V \to H,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right), \operatorname{inv}\left(\operatorname{phi}\left(i\right)\right) \cdot \operatorname{phi}\left(j\right)\right) \le 2 \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.intervalGraph_isChordal_and_two_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every nonempty subset of vertices, the interval with least right endpoint has pairwise intersecting neighbors in that subset. Applied to the support of a cycle, this gives a chord. For gain reconstruction begin at an interval with least left endpoint and fit all edges from that root exactly. Retain a neighbor of largest right endpoint and remove the rest of the closed neighborhood. The retained vertex has its left endpoint at most every remaining right endpoint. Repeat with this vertex as root, renormalizing the recursive potential at it. For any edge from the old neighborhood to the remaining vertices, its interval overlap forces both endpoints to meet the retained vertex. One triangle compares the two root spokes and the other compares the crossing edge against the path through the retained vertex. If the root has no neighbors it can be removed without an edge constraint. The group metric is invariant under both left and right multiplication. Reversal of an edge inverts its gain, so the ordered triangle condition is equivalent to bounding the distance of the triangle product from the identity.

**Theorem 1.3 (Split graphs).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall H \in \operatorname{Type}\left(v\right),\; [\operatorname{Finite}\left(V\right)] [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(\operatorname{MulOpposite}\left(H\right), H\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall C \in \operatorname{Set}\left(V\right),\; (\operatorname{IsClique}\left(G, C\right)) \Rightarrow ((\operatorname{IsIndepSet}\left(G, \operatorname{compl}\left(C\right)\right)) \Rightarrow (\forall g \in V \to \left(V \to H\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(j, i\right) = \operatorname{inv}\left(\operatorname{g}\left(i, j\right)\right))) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right) \cdot \operatorname{g}\left(j, l\right), \operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow ((\operatorname{IsChordal}\left(G\right)) \land (\exists phi \in V \to H,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(i, j\right), \operatorname{inv}\left(\operatorname{phi}\left(i\right)\right) \cdot \operatorname{phi}\left(j\right)\right) \le 2 \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.exists_two_approximate_gain_potential_of_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In each nonempty vertex subset, a vertex outside the clique, if present, has all its neighbors in the clique. Otherwise the subset is a clique. This gives chordality by taking the subset of vertices of a cycle. Choose a root of the clique if it is nonempty and assign each other clique vertex the gain from the root. Each non-clique vertex of positive degree is assigned the potential of any clique neighbor multiplied by the connecting gain. On clique edges the error is at most one triangle defect, and on any other edge the triangle through the chosen attachment and the clique comparison together cost at most two defects. Isolated vertices may be assigned arbitrary values.

**Theorem 1.4 (Path powers are interval graphs).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \exists l \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \exists r \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(n\right),\; (\operatorname{l}\left(i\right) = \operatorname{real}\left(\operatorname{val}\left(i\right)\right)) \land (\operatorname{r}\left(i\right) = \operatorname{real}\left(\operatorname{val}\left(i\right)\right)+\operatorname{real}\left(k\right))) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{l}\left(i\right) \le \operatorname{r}\left(i\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (\operatorname{Adj}\left(\operatorname{pathPower}\left(n, k\right), i, j\right)) \Leftrightarrow ((i \neq j) \land (\operatorname{max}\left(\operatorname{l}\left(i\right), \operatorname{l}\left(j\right)\right) \le \operatorname{min}\left(\operatorname{r}\left(i\right), \operatorname{r}\left(j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.pathPower_isIntervalGraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path power on Fin(n) joins distinct indices x and y when each is at most k greater than the other. The closed intervals from i to i plus k intersect exactly under these two inequalities. Thus the path-power lower bounds for Banach reconstruction are attained in the class of finite interval graphs. In the frozen lower bound the length factor tends to one at each fixed width, while the limiting width coefficient tends to two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.exists_simplicial_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.exists_two_approximate_gain_potential_of_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.intervalGraph_isChordal_and_two_approximate_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.pathPower_isIntervalGraph`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo](ChordalBanachLimitTwo.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential](UniformGainPotential.md)
