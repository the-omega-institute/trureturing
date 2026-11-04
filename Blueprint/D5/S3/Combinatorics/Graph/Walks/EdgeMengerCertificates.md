# Finite edge-Menger certificates

## Abstract

Finite edge-deletion resilience is equivalent to pairwise edge-disjoint path certificates.

**Theorem 1.1 (Deletion resilience and edge-disjoint paths).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathrm{Nat},\; \forall u \in V,\; \forall v \in V,\; \left(\forall S \in \operatorname{Set}\left(\operatorname{Sym2}\left(V\right)\right),\; \operatorname{encard}\left(S\right) < \operatorname{NatToENat}\left(k\right) \Rightarrow \operatorname{Reachable}\left(\operatorname{deleteEdges}\left(G, S\right), u, v\right)\right) \Leftrightarrow \left(\exists p \in \operatorname{WalkFamily}\left(G, u, v, k\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{IsPath}\left(\operatorname{p}\left(i\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; i \ne j \Rightarrow \operatorname{ListDisjoint}\left(\operatorname{edges}\left(\operatorname{p}\left(i\right)\right), \operatorname{edges}\left(\operatorname{p}\left(j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates.isEdgeReachable_iff` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and finite Menger certificates: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

For every vertex type V in any universe with Finite(V), every simple undirected graph G on V, every natural number k, and all vertices u and v, the native G.IsEdgeReachable(k,u,v) is equivalent to a family p indexed by Fin(k) of G-walks from u to v, each satisfying IsPath, whose edge lists are pairwise List.Disjoint at distinct indices.

The left side is displayed with the native definition expanded: for every S : Set(Sym2(V)), if encard(S) is strictly less than the natural k coerced to ENat, u and v are reachable in G.deleteEdges(S). S ranges over all sets of unordered vertex pairs, including pairs that are not graph edges. The theorem concerns natural k, not arbitrary infinite ENat thresholds. WalkFamily(G,u,v,k) in the formula means the function type Fin(k) to G.Walk(u,v). ListDisjoint is List.Disjoint of the two complete unordered edge lists.

The scope includes k=0, u=v, an empty vertex type, edge-free graphs, adjacent endpoints and zero-length paths. For u=v the certificate is the constant family of nil paths for every k; distinct indices need not denote distinct walks. Edge-disjoint paths may share internal vertices. No connectedness, nonempty-graph, endpoint-nonadjacency or positive-length assumption is imposed. Directed, infinite-vertex and vertex-disjoint variants are outside this statement.

For distinct endpoints, apply the first conjunct of the public MengerCertificates.exists_separator_paths_and_weak_duality directly to G.lineGraph. Its vertices are actual edges of G, and its terminal sets consist of the edges incident to u and v; these sets may overlap. Project a line-graph separator to an edge-deletion set. A surviving deleted-graph walk lifts to a line-graph walk with controlled support, contradicting separation unless k is at most the separator size. Lower the resulting vertex-disjoint line walks to original walks, then bypass them to paths while preserving edge containment and hence edge disjointness. Restrict indices with Fin.castLE. A nil line walk can lower to a single original edge for distinct adjacent endpoints. The reverse direction chooses a deleted edge met by each walk; disjointness makes this choice injective and contradicts encard(S)<k.

The received proof source is Juan Pablo Traverso Gianini's jtraverso/menger-hamiltonian, immutable commit 35c5f684f9bfbd244bd0999ce725623ab571adb6: MengerCore.lean's lift_to_lineGraph, walk_in_edge and lower_from_lineGraph, and Menger.lean's isEdgeReachable_iff. The source attributes Menger's theorem to Diestel, Graph Theory, Theorem 3.3.1, second proof (Boehme, Goering, Harant). The receiver uses its frozen public vertex certificate instead of duplicating that proof. This is known mathematics with credited source reception; no originality or reading of the original Diestel text is claimed.

The source copyright and complete Apache license are retained in the Lean source and docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Retire this port only when this repository's own adopted Mathlib pin supplies the equivalent full finite edge theorem and affected consumers and records migrate lawfully.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates.isEdgeReachable_iff`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MengerCertificates](MengerCertificates.md)
