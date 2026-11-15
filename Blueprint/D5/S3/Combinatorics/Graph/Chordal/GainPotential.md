# Group potentials from triangle consistency

## Abstract

Triangle-compatible group labels on a finite chordal graph admit a global vertex potential.

Let G be a finite simple graph and H an arbitrary group. The label g(i,j) is attached to the oriented edge from i to j. Reversal inverts the label. On each triangle, the ordered product g(i,j)g(j,k) equals g(i,k). A potential assigns a group element to each vertex so that every edge label is the inverse source potential multiplied by the target potential.

**Theorem 1.1 (A global potential on every finite chordal graph).**

$$\forall V \in \operatorname{Type}\left(u\right),\; \forall H \in \operatorname{Type}\left(v\right),\; [\operatorname{Finite}\left(V\right)] [\operatorname{Group}\left(H\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in V \to \left(V \to H\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(j, i\right) = \operatorname{inv}\left(\operatorname{g}\left(i, j\right)\right))) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall k \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, k\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, k\right)) \Rightarrow (\operatorname{g}\left(i, j\right) * \operatorname{g}\left(j, k\right) = \operatorname{g}\left(i, k\right))))) \Rightarrow (\exists phi \in V \to H,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{g}\left(i, j\right) = \operatorname{inv}\left(\operatorname{phi}\left(i\right)\right) * \operatorname{phi}\left(j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/GainPotential.exists_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Chordality means that every cycle of length at least four has a chord. The group may be noncommutative, and the vertex type may lie in any universe. The theorem includes the empty graph and graphs with several connected components. The gain function is total, but its values on nonedges and on the diagonal are unrestricted.

Induct on a finite set of vertices. A simplicial vertex x has pairwise adjacent neighbors in the induced graph. Remove x and obtain a potential psi on the remaining vertices. If x has no remaining neighbor, its potential can be assigned freely. Otherwise choose a neighbor w and set the potential at x to psi(w) times the inverse of g(x,w). For each other neighbor j, simpliciality supplies the edge from w to j, and the triangle relation shows that this same assignment satisfies the edge from x to j. Reversal supplies the opposite orientation. Reinsert x without changing any of the other potential values.

The argument uses associativity and inverses without commuting factors. It applies to phase synchronization by taking a phase group, and to permutation synchronization by taking a permutation group. These interpretations require the stated exact triangle relations. They supply no estimate for inconsistent or noisy labels, no uniqueness across components, and no algorithmic running-time bound.

Group gains, balance and switching are classical gain-graph notions. Zaslavsky's Lectures on Gain Graphs and Hyperplane Arrangements, Definitions 1, 3, 4 and 10 and Propositions 7, 11, 12 and 13, describe their background: https://people.math.binghamton.edu/zaslav/Tpapers/gaingraphs-lecture-notes.pdf . Here the sufficient local condition is triangle consistency on a chordal graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/GainPotential.exists_gain_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
