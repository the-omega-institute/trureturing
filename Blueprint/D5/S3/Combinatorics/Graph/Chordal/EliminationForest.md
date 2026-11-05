# Elimination rankings and rooted clique forests

## Abstract

The universe u is arbitrary. IsPEO(G,ord) has exactly two fields: ord is injective, and for each v the set of neighbors u with ord(v) < ord(u) is a clique. RelativeSimplicial(G,S,z) means that for all distinct a,b in S, adjacency of z to a and b implies adjacency of a to b. Nonempty(S) means that S contains an element. EliminatesEveryFiniteSet(G) says that each nonempty finite set contains such a z. LaterIn(G,S,f,v) is exactly the set of u in S with f(v) < f(u) and G.Adj v u.

**Theorem 1.1 (Simpliciality inside each finite set).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{IsChordal}\left(G\right) \Rightarrow \left(\forall S \in \mathrm{Finset}\left(V\right),\; \mathrm{Nonempty}\left(S\right) \Rightarrow \left(\exists z \in V,\; z \in S \land \mathrm{RelativeSimplicial}\left(G, S, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_simplicial_in_finset` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Apply Dirac to the induced graph on the finite set. Neither a finite ambient vertex type nor a nonempty ambient type is assumed.

**Theorem 1.2 (Erase-and-shift rank construction).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{EliminatesEveryFiniteSet}\left(G\right) \Rightarrow \left(\forall n \in \mathrm{Nat},\; \forall S \in \mathrm{Finset}\left(V\right),\; \mathrm{card}\left(S\right) = n \Rightarrow \left(\exists f \in V \to \mathrm{Nat},\; \mathrm{InjOn}\left(f, S\right) \land \left(\forall v \in V,\; v \in S \Rightarrow \mathrm{IsClique}\left(G, \mathrm{LaterIn}\left(G, S, f, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_rank_of_simplicial_elimination` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

At cardinality zero the constant zero function suffices on the empty set. At a successor cardinality, remove a relatively simplicial vertex, rank it zero, and increase every remaining rank by one. The ranking is injective on the chosen set; no bound on its values is part of the conclusion.

**Theorem 1.3 (Perfect elimination of finite chordal graphs).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Finite}\left(V\right) \Rightarrow \left(\mathrm{IsChordal}\left(G\right) \Rightarrow \left(\exists ord \in V \to \mathrm{Nat},\; \mathrm{IsPEO}\left(G, ord\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_isPEO` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

An internal Fintype choice applies the rank construction to the full vertex set. The public hypothesis is Finite only. The clique-forest construction attaches the bag consisting of a vertex and its later neighbors, with the earliest later neighbor as its Option-valued parent. A count of vertices with higher rank decreases toward each root and distinguishes nodes. Local bag inheritance gives the ancestor/intersection property. Multiple roots and an empty vertex type require no additional connector.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_isPEO`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_rank_of_simplicial_elimination`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_simplicial_in_finset`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
