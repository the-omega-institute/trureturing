# Gain reconstruction on clique trees

## Abstract

Potential reconstruction on finite clique trees.

**Theorem 1.1 (Center extension).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall w \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)], \forall I \in \operatorname{Type}\left(w\right),\; [\operatorname{Finite}\left(I\right)], \forall T \in \operatorname{SimpleGraph}\left(I\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall K \in I \to \operatorname{Set}\left(V\right),\; (\operatorname{IsCliqueTree}\left(T, G, K\right)) \Rightarrow ((\forall a \in I,\; \forall b \in I,\; (\operatorname{Adj}\left(T, a, b\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{K}\left(a\right), \operatorname{K}\left(b\right)\right)\right))) \Rightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\forall a \in I,\; \forall b \in I,\; (\operatorname{Adj}\left(T, a, b\right)) \Rightarrow (\operatorname{ncard}\left(\operatorname{intersection}\left(\operatorname{K}\left(a\right), \operatorname{K}\left(b\right)\right)\right) \le m)) \Rightarrow (\forall D \in \mathbb{N},\; (\forall a \in I,\; \forall b \in I,\; \operatorname{dist}\left(T, a, b\right) \le D) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)], \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall x \in V,\; \forall y \in V,\; \operatorname{g}\left(y, x\right) = -\operatorname{g}\left(x, y\right)) \Rightarrow ((\forall t \in V,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{Adj}\left(G, t, x\right)) \Rightarrow ((\operatorname{Adj}\left(G, x, y\right)) \Rightarrow ((\operatorname{Adj}\left(G, t, y\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(t, x\right)+\operatorname{g}\left(x, y\right)-\operatorname{g}\left(t, y\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{Adj}\left(G, x, y\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(x, y\right)-(\operatorname{phi}\left(y\right)-\operatorname{phi}\left(x\right))\right) \le \operatorname{cliqueTreeRadius}\left(m, 1, \operatorname{natDiv}\left(D, 2\right)\right) \cdot epsilon)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential.cliqueTree_center_extension_banach_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A clique tree consists of a tree T and clique bags K that cover every vertex and edge of G. Every bag on a tree path between two occurrences of a vertex contains that vertex. The separator of adjacent bags is their intersection. The functions dist and ncard denote graph distance and finite cardinality.

Start with radius coefficient one on a central clique or central edge. On one clique the mean of all its stars has the sharper local coefficient one minus two divided by its size on every edge. On a central edge, average the stars from the shared separator to obtain the coefficient one on both bags.

Extend the potential into each successive layer by averaging the candidates obtained by extending the old values at the parent separator along an edge. When one endpoint of an edge is old, its own candidate has zero error. Each other candidate costs at most the old residual plus one triangle defect. The recurrence takes the maximum of the old coefficient, one for edges with two new endpoints, and the mixed-edge coefficient.

**Theorem 1.2 (Gluing at separator midpoints).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall w \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)], \forall I \in \operatorname{Type}\left(w\right),\; [\operatorname{Finite}\left(I\right)], \forall T \in \operatorname{SimpleGraph}\left(I\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall K \in I \to \operatorname{Set}\left(V\right),\; (\operatorname{IsCliqueTree}\left(T, G, K\right)) \Rightarrow ((\forall a \in I,\; \forall b \in I,\; (\operatorname{Adj}\left(T, a, b\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{K}\left(a\right), \operatorname{K}\left(b\right)\right)\right))) \Rightarrow ((\forall x \in V,\; \operatorname{ncard}\left(\operatorname{fiberMembership}\left(K, x, I\right)\right) \le 2) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)], \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall x \in V,\; \forall y \in V,\; \operatorname{g}\left(y, x\right) = -\operatorname{g}\left(x, y\right)) \Rightarrow ((\forall t \in V,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{Adj}\left(G, t, x\right)) \Rightarrow ((\operatorname{Adj}\left(G, x, y\right)) \Rightarrow ((\operatorname{Adj}\left(G, t, y\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(t, x\right)+\operatorname{g}\left(x, y\right)-\operatorname{g}\left(t, y\right)\right) \le epsilon)))) \Rightarrow ((\operatorname{cliqueTreeMidpointCoeff}\left(T, K\right) < 3) \land (\exists phi \in V \to E,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{Adj}\left(G, x, y\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(x, y\right)-(\operatorname{phi}\left(y\right)-\operatorname{phi}\left(x\right))\right) \le \operatorname{cliqueTreeMidpointCoeff}\left(T, K\right) \cdot epsilon))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential.cliqueTree_twoClique_midpoint_banach_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For adjacent bags the separator coefficient is the product of one minus the reciprocal of the separator size and one minus the separator size divided by the larger bag size. The midpoint coefficient is the largest sum of the clique star coefficient and the two largest incident separator coefficients, padding missing terms with zero. A graph without edges has coefficient zero.

Translate the clique means so their difference on each separator has mean zero. In the difference of the two star residuals, the common triangle term from each shared star cancels with weight equal to the reciprocal of the larger clique size. Taking the mean of the remaining increments and dropping the zero diagonal term yields the separator coefficient for the midpoint displacement.

An edge with both endpoints in a single separator has the averaged residual of its two cliques. When the endpoints lie in different separators, their shifts are bounded by the two largest distinct incident coefficients. The finite maximum of the resulting local coefficients is strictly below three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential.cliqueTree_center_extension_banach_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential.cliqueTree_twoClique_midpoint_banach_potential`
