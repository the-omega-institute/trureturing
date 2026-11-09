# Terminal-clean fans

## Abstract

Deletion connectivity produces paths to distinct terminals sharing only their source.

**Theorem 1.1 (A fan of the full minimum size).**

$$\forall V \in \operatorname{Type}\left(\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \left(\forall S \in \operatorname{Set}\left(V\right),\; \operatorname{ncard}\left(S\right) < k \Rightarrow \operatorname{Connected}\left(\operatorname{induce}\left(G, \operatorname{compl}\left(S\right)\right)\right)\right) \Rightarrow \left(\forall B \in \operatorname{Finset}\left(V\right),\; \forall x \in V,\; \left(\neg x \in B\right) \Rightarrow \left(\exists e \in \operatorname{Fin}\left(\operatorname{min}\left(k, \operatorname{card}\left(B\right)\right)\right) \to V,\; \exists P \in \operatorname{WalkFamily}\left(G, x, e\right),\; \left(\forall i \in \operatorname{Fin}\left(\operatorname{min}\left(k, \operatorname{card}\left(B\right)\right)\right),\; \operatorname{e}\left(i\right) \in B \land \left(\operatorname{IsPath}\left(\operatorname{P}\left(i\right)\right) \land \left(\forall y \in V,\; y \in \operatorname{support}\left(\operatorname{P}\left(i\right)\right) \Rightarrow \left(y \in B \Rightarrow y = \operatorname{e}\left(i\right)\right)\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(\operatorname{min}\left(k, \operatorname{card}\left(B\right)\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{min}\left(k, \operatorname{card}\left(B\right)\right)\right),\; i \ne j \Rightarrow \left(\forall y \in V,\; y \in \operatorname{support}\left(\operatorname{P}\left(i\right)\right) \Rightarrow \left(y \in \operatorname{support}\left(\operatorname{P}\left(j\right)\right) \Rightarrow y = x\right)\right)\right) \land \operatorname{Injective}\left(e\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_fan` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Let V be a finite type in any universe, G a simple undirected graph on V, and k a natural number. Suppose that deleting any vertex set S of cardinality less than k leaves a connected induced graph. For every finite terminal set B and every vertex x outside B, there are exactly min(k, |B|) paths from x to distinct vertices of B. Each path meets B only at its endpoint, and two different paths share no vertex other than x.

The endpoint function e has domain Fin(min(k, |B|)); P(i) is an actual walk from x to e(i), required to be a path. Cleanliness quantifies over the full support of P(i). Pairwise intersection also uses full supports, so terminal distinctness is included explicitly. No positive lower bound on k or on |B| is assumed. If either is zero, the indexed family is empty.

Remove the edges incident with x, and take A to be the neighbors of x. Every A-to-B separator X in this graph has cardinality at least min(k, |B|): otherwise choose a terminal outside X and use connectivity after deleting X without x. A path from x to that terminal has a first neighbor in A; its remaining path avoids x and contradicts separation by X. Terminal-clean Menger certificates therefore supply min(k, |B|) mutually disjoint A-to-B paths. Prepending their edges from x gives the fan. Their original disjointness and the isolation of x ensure that the new paths share only x.

For an ordinary cycle C, taking B to be its vertex support gives a fan of size min(k, C.length), since a cycle has as many distinct vertices as edges. This cardinality does not assert that C spans the ambient vertex type or that C.length is at least k.

**Theorem 1.2 (A maximal ordinary cycle and its fans).**

$$\forall V \in \operatorname{Type}\left(\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \operatorname{Nat}\left(\right),\; 3 \le \operatorname{card}\left(V\right) \Rightarrow \left(2 \le k \Rightarrow \left(\left(\forall S \in \operatorname{Set}\left(V\right),\; \operatorname{ncard}\left(S\right) < k \Rightarrow \operatorname{Connected}\left(\operatorname{induce}\left(G, \operatorname{compl}\left(S\right)\right)\right)\right) \Rightarrow \left(\exists a \in V,\; \exists C \in \operatorname{Walk}\left(G, a, a\right),\; \operatorname{IsCycle}\left(C\right) \land \left(\left(\forall b \in V,\; \forall D \in \operatorname{Walk}\left(G, b, b\right),\; \operatorname{IsCycle}\left(D\right) \Rightarrow \operatorname{length}\left(D\right) \le \operatorname{length}\left(C\right)\right) \land \left(\forall x \in V,\; \left(\neg x \in \operatorname{support}\left(C\right)\right) \Rightarrow \operatorname{Fan}\left(G, x, \operatorname{support}\left(C\right), \operatorname{min}\left(k, \operatorname{length}\left(C\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_maximal_cycle_fans` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Assume additionally that V has at least three vertices and k is at least two. There exists an actual closed G-walk C that is a cycle, and every actual cycle in G has length at most C.length. For each vertex x outside the support, an actual fan of exactly min(k, C.length) paths has distinct endpoints on C, is terminal-clean with respect to C, and has pairwise intersection only at x. All these clauses concern the same chosen cycle C.

A cycle exists because deletion connectivity forces every vertex to have degree at least two. An acyclic connected graph would be a tree; its edge count contradicts the sum of these degree bounds. Cycle length is bounded by the number of vertices, so a greatest attained length exists. Applying the fan theorem to that support gives the stated size and cleanliness.

In the formula, Fan(G,x,B,r) is the existential endpoint-and-walk statement of the preceding theorem with index type Fin(r), including pathhood, terminal cleanliness, pairwise intersection only at x and injective endpoints. This theorem neither asserts that the maximal cycle spans V nor that its length is at least k.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_fan`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_maximal_cycle_fans`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/ColoringExtension](../Brooks/ColoringExtension.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MengerCertificates](MengerCertificates.md)
