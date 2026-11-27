# Chordal reconstruction by retained simplicial identities

## Abstract

Old triangle differences and two retained identities bound chordal gain residuals.

**Theorem 1.1 (Old triangle regrouping).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow ((\forall C \in \operatorname{Set}\left(V\right),\; (\operatorname{IsClique}\left(G, C\right)) \Rightarrow (\operatorname{ncard}\left(C\right) \le k + 1)) \Rightarrow (\forall radius \in \mathbb{R},\; (\operatorname{max}\left(1, \operatorname{real}\left(k\right) - 2\right) \le radius) \Rightarrow ((radius \le \operatorname{real}\left(k\right) - 1) \Rightarrow ((2 \cdot (\operatorname{real}\left(k\right) - 1) \le radius \cdot (radius + 1)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)], \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) + \operatorname{g}\left(j, l\right) - \operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) - (\operatorname{phi}\left(j\right) - \operatorname{phi}\left(i\right))\right) \le (radius) \cdot epsilon))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_regrouped_simplicial_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse a perfect elimination order so that each earlier neighborhood is a clique. Assign each potential by averaging the earlier potentials plus their gains into the new vertex. The weights are uniform below k predecessors. At k predecessors, the first k minus one weights are s and the last is t, where s is the reciprocal of one plus R and the weights sum to one.

The retained weighted residual at each vertex is zero. For the edge from the newest predecessor of a full neighborhood, its own earlier clique contains the other predecessors. If it contains one extra vertex, subtract its retained identity and pair the residual at that extra vertex with the residual at its newest predecessor. The old triangle bounds the difference by R plus one times epsilon. This gives the quadratic closing condition. The operator real denotes the natural-number cast.

**Theorem 1.2 (Two identities for clique size six).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow ((\forall C \in \operatorname{Set}\left(V\right),\; (\operatorname{IsClique}\left(G, C\right)) \Rightarrow (\operatorname{ncard}\left(C\right) \le 6)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)], \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) + \operatorname{g}\left(j, l\right) - \operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) - (\operatorname{phi}\left(j\right) - \operatorname{phi}\left(i\right))\right) \le (2 \cdot \operatorname{sqrt}\left(3\right) - 1) \cdot epsilon))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_multiIdentity_cliqueSix_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Average uniformly for at most three predecessors. For four or five, use weights s, s, s, t followed by zeros. Here s is the reciprocal of two times the square root of three and t is one minus three times s.

In the exceptional edge of weight t, the three older current predecessors include one primary vertex, the former fourth vertex and the former fifth vertex. Subtract the retained identity at the current endpoint and eliminate the residual at the former fifth vertex using its own identity. For an extra predecessor of that vertex, the auxiliary vector is the sum of the residual at the eliminated vertex and the residual from that vertex to its extra predecessor. The auxiliary distances and shared triangle defects together cost the coefficient used in the elimination.

**Theorem 1.3 (Two identities for clique size seven).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow ((\forall C \in \operatorname{Set}\left(V\right),\; (\operatorname{IsClique}\left(G, C\right)) \Rightarrow (\operatorname{ncard}\left(C\right) \le 7)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)], \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) + \operatorname{g}\left(j, l\right) - \operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right) - (\operatorname{phi}\left(j\right) - \operatorname{phi}\left(i\right))\right) \le (\frac{3 + \operatorname{sqrt}\left(7\right)}{2}) \cdot epsilon))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_multiIdentity_cliqueSeven_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the three equal leading weights s, then t, then zeros in predecessor cliques of size four through six. For the two exceptional edges of weight t, eliminate the contribution from the last vertex of the old six-vertex predecessor clique by its retained identity.

The decisive edge has weight zero and omits two primary vertices of its earlier clique. Eliminate the contribution of its newest predecessor with coefficient t. The resulting negative mass is at most twice s minus t times s plus t, with the latter product subtracted as a whole. The bound closes by the quadratic equation for the displayed radius.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_multiIdentity_cliqueSeven_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_multiIdentity_cliqueSix_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.exists_regrouped_simplicial_banach_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/EliminationForest](EliminationForest.md)
