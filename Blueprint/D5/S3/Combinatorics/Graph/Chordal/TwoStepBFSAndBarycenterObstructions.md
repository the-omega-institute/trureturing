# Obstructions to breadth-first gain reconstruction

## Abstract

Two finite chordal graph families force large errors for breadth-first reconstruction.

**Theorem 1.1 (Pure predecessor averaging has unbounded error).**

$$(\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (2 \le m) \Rightarrow ((1 \le n) \Rightarrow (((\operatorname{Chordal}\left(\operatorname{Tower}\left(m, n\right)\right)) \land ((\operatorname{Connected}\left(\operatorname{Tower}\left(m, n\right)\right)) \land (\operatorname{Flat}\left(\operatorname{Tower}\left(m, n\right), \operatorname{TowerGain}\left(m, n\right)\right)))) \land ((\exists phi \in \operatorname{TowerVertices}\left(m, n\right) \to \mathbb{R},\; \operatorname{Pure}\left(\operatorname{Tower}\left(m, n\right), \operatorname{Root}\left(\right), \operatorname{TowerGain}\left(m, n\right), phi\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; (\operatorname{dist}\left(\operatorname{Tower}\left(m, n\right), \operatorname{Root}\left(\right), \operatorname{LayerVertex}\left(i, j\right)\right) = i+1) \land (\forall phi \in \operatorname{TowerVertices}\left(m, n\right) \to \mathbb{R},\; (\operatorname{Pure}\left(\operatorname{Tower}\left(m, n\right), \operatorname{Root}\left(\right), \operatorname{TowerGain}\left(m, n\right), phi\right)) \Rightarrow (\operatorname{eval}\left(phi, \operatorname{LayerVertex}\left(i, j\right)\right) = \operatorname{ifzero}\left(j, 0, 2\cdot\operatorname{real}\left(m\right)-1-(2\cdot\operatorname{real}\left(m\right)-2)\cdot(\frac{\operatorname{real}\left(m\right)-1}{\operatorname{real}\left(m\right)})^{i}\right)))))))) \land (\forall M \in \mathbb{R},\; \exists m \in \mathbb{N},\; \exists n \in \mathbb{N},\; (2 \le m) \land ((1 \le n) \land (((\operatorname{Chordal}\left(\operatorname{Tower}\left(m, n\right)\right)) \land ((\operatorname{Connected}\left(\operatorname{Tower}\left(m, n\right)\right)) \land (\operatorname{Flat}\left(\operatorname{Tower}\left(m, n\right), \operatorname{TowerGain}\left(m, n\right)\right)))) \land (\exists u \in \operatorname{TowerVertices}\left(m, n\right),\; \exists v \in \operatorname{TowerVertices}\left(m, n\right),\; (\operatorname{Adj}\left(\operatorname{Tower}\left(m, n\right), u, v\right)) \land (\forall phi \in \operatorname{TowerVertices}\left(m, n\right) \to \mathbb{R},\; (\operatorname{Pure}\left(\operatorname{Tower}\left(m, n\right), \operatorname{Root}\left(\right), \operatorname{TowerGain}\left(m, n\right), phi\right)) \Rightarrow (M < \lvert \operatorname{eval}\left(\operatorname{TowerGain}\left(m, n\right), u, v\right)-(\operatorname{eval}\left(phi, v\right)-\operatorname{eval}\left(phi, u\right))\rvert ))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions.pure_predecessor_barycenter_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tower has a root and n layers of m vertices. Each layer is a clique with one distinguished vertex at column zero. The first layer is adjacent to the root. From the next layer onward, column zero has only its distinguished predecessor, and each other vertex is adjacent to the entire preceding layer. Eliminating layers in reverse order, with column zero first in each layer, proves chordality. Edges change the layer by at most one and every vertex has a path down to the root.

TowerGain is zero within layers and into the distinguished column, one on the remaining edges from the root or column zero, and two on the remaining edges. Reverse orientations have the opposite gain. Flat means skew with absolute triangle defect at most one. The two gains across any triangle spanning two consecutive layers differ by at most one.

Pure means zero potential at the root and, at each vertex with predecessors, the arithmetic mean of predecessor potential plus incoming gain. Column zero has potential zero. Each other column starts at one and the next value is the sum of one and m minus one copies of the previous value plus two, divided by m. This recurrence has the displayed closed form. The within-layer edge from column zero realizes the value as its absolute residual. For fixed m these values approach twice m minus one.

**Theorem 1.2 (Averaging over roots permits residuals approaching four).**

$$\forall m \in \mathbb{N},\; \forall N \in \mathbb{N},\; (2 \le m) \Rightarrow ((2 \le N) \Rightarrow ((\operatorname{Chordal}\left(\operatorname{Gadget}\left(m, N\right)\right)) \land ((\operatorname{Connected}\left(\operatorname{Gadget}\left(m, N\right)\right)) \land (\forall mu \in \operatorname{GadgetVertices}\left(m, N\right) \to \mathbb{R},\; (\forall r \in \operatorname{GadgetVertices}\left(m, N\right),\; 0 \le \operatorname{eval}\left(mu, r\right)) \Rightarrow ((\operatorname{Sum}\left(\operatorname{GadgetVertices}\left(m, N\right), mu\right) = 1) \Rightarrow (\forall a \in \operatorname{RootIndexedAnchors}\left(\operatorname{Gadget}\left(m, N\right)\right),\; \forall w \in \operatorname{GadgetVertices}\left(m, N\right) \to \left(\operatorname{GadgetVertices}\left(m, N\right) \to \left(\operatorname{GadgetVertices}\left(m, N\right) \to \mathbb{R}\right)\right),\; (\forall r \in \operatorname{GadgetVertices}\left(m, N\right),\; \operatorname{Anchors}\left(\operatorname{Gadget}\left(m, N\right), r, \operatorname{eval}\left(a, r\right)\right)) \Rightarrow ((\forall r \in \operatorname{GadgetVertices}\left(m, N\right),\; \operatorname{Weights}\left(\operatorname{Gadget}\left(m, N\right), r, \operatorname{eval}\left(w, r\right)\right)) \Rightarrow (\exists g \in \operatorname{GadgetVertices}\left(m, N\right) \to \left(\operatorname{GadgetVertices}\left(m, N\right) \to \mathbb{R}\right),\; (\operatorname{Flat}\left(\operatorname{Gadget}\left(m, N\right), g\right)) \land (\exists u \in \operatorname{GadgetVertices}\left(m, N\right),\; \exists v \in \operatorname{GadgetVertices}\left(m, N\right),\; (\operatorname{Adj}\left(\operatorname{Gadget}\left(m, N\right), u, v\right)) \land (4-\frac{4}{\operatorname{real}\left(m\right)}-\frac{8}{\operatorname{real}\left(N\right)} \le \lvert \operatorname{eval}\left(g, u, v\right)-(\operatorname{Mean}\left(\operatorname{Gadget}\left(m, N\right), mu, a, w, g, v\right)-\operatorname{Mean}\left(\operatorname{Gadget}\left(m, N\right), mu, a, w, g, u\right))\rvert ))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions.twoStepBFS_root_averaging_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gadget joins N copies along a path through their roots. In each copy the root meets A, the union of A and U is a clique, each v meets U and its matching vertex in A, and each y meets U and its matching v. Each indexed part has m vertices. The y vertices, then the v vertices, then U, then A, and finally the roots in path order give an elimination order.

Anchors associates each component outside a root ball with a common predecessor of its shadow in the parent shadow, using the root at depth one. Weights gives each nonroot vertex a probability distribution supported on its BFS predecessors. The root potential is zero. At every other vertex the potential transports along successive anchors and adds the weighted mean of the gains on the two-edge paths from the anchor through the predecessors. Mean is the sum of these potentials weighted by the root law.

A copy of root mass at most one over N exists by averaging. For any root outside that copy, distances in the copy increase by the distance to the copy root. The predecessors of each u are A, while the predecessors of each y are U and its matching v. The component of y in its tail consists of y alone, with shadow U and its matching v. The parent shadow is A. Its intersection with the earlier neighbors of the matching v forces the anchor for y to be the matching vertex in A, and the parent anchor is the copy root.

Summing the two distinguished predecessor weights over all pairs of u and y gives at most twice m for each exterior root. Some pair has exterior mean total distinguished weight at most two over m. Ordering the vertices and assigning unit forward and negative unit backward gains gives defect one. The signed residual for each exterior root is four minus twice each distinguished weight. The general four-defect estimate bounds the absolute residual for each interior root. Combining the two root contributions yields the displayed coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions.pure_predecessor_barycenter_unbounded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions.twoStepBFS_root_averaging_lower_bound`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS](Reconstruction/WeightedTwoStepBFS.md)
