# Chordal graphs and simplicial vertices

## Abstract

The vertex type may lie in any universe u. IsChordal means that every cycle of length at least four has an adjacency between two supported vertices whose unordered edge is absent from that cycle. IsSimplicial means that the entire neighbor set is a clique.

**Theorem 1.1 (Induced-subgraph heredity).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{IsChordal}\left(G\right) \Rightarrow \left(\forall W \in \mathrm{Set}\left(V\right),\; \mathrm{IsChordal}\left(\mathrm{induce}\left(G, W\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Dirac.induce` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Pulling a cycle through the subtype embedding preserves its cycle property and support and transfers a chord back to the induced graph. No finiteness hypothesis is needed.

**Theorem 1.2 (Dirac simplicial-vertex theorem).**

$$\forall V \in \mathrm{Type}\left(u\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Finite}\left(V\right) \Rightarrow \left(\mathrm{Nonempty}\left(V\right) \Rightarrow \left(\mathrm{IsChordal}\left(G\right) \Rightarrow \left(\exists v \in V,\; \mathrm{IsSimplicial}\left(G, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Dirac.exists_isSimplicial` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

A nonempty finite chordal graph has a simplicial vertex. The cardinal induction handles complete graphs, a proper connected component in the disconnected case, and a minimal separator in the remaining case. Minimal separators are cliques because two internally disjoint induced paths would otherwise form a chordless cycle. The result uses classical existence and gives no running-time bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Dirac.exists_isSimplicial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Dirac.induce`
