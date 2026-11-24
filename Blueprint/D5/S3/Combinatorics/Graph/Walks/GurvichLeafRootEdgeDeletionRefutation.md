# Deleting a leaf root edge can destroy inherence

## Abstract

Deleting the edge at the first root of an inherent six-vertex path leaves a two-rooted graph that a nine-vertex tree confines.

**Definition 1.1 (Conjecture 6.4).**

$$\forall (n : \mathbb{N}), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (s : \operatorname{Fin}\left(n\right)), \forall (t : \operatorname{Fin}\left(n\right)), \forall (u : \operatorname{Fin}\left(n\right)), (\operatorname{degree}\left(H, s\right) \le \operatorname{degree}\left(H, t\right)) \Rightarrow \left((s \ne t) \Rightarrow \left((\forall (v : \operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(H, s, v\right) \Leftrightarrow v = u) \Rightarrow \left((\forall (m : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\operatorname{Nonempty}\left(\operatorname{Copy}\left(H, G\right)\right)) \Rightarrow \exists (f : \operatorname{Copy}\left(H, G\right)), \forall (x : \operatorname{Fin}\left(m\right)), \forall (y : \operatorname{Fin}\left(m\right)), (\left(\neg x \in \operatorname{range}\left(f\right)\right) \land \left(\left(\neg y \in \operatorname{range}\left(f\right)\right) \land \left(x \ne y \land \left(\operatorname{Adj}\left(G, f\left(s\right), x\right) \land \operatorname{Adj}\left(G, f\left(t\right), y\right)\right)\right)\right)) \Rightarrow \operatorname{Reachable}\left(\operatorname{induce}\left(G, \operatorname{Fin}\left(m\right) \setminus \operatorname{range}\left(f\right)\right), x, y\right)) \Rightarrow \forall (m : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\operatorname{Nonempty}\left(\operatorname{Copy}\left(\operatorname{deleteEdges}\left(H, \{\operatorname{Sym2.mk}\left(s, u\right)\}\right), G\right)\right)) \Rightarrow \exists (f : \operatorname{Copy}\left(\operatorname{deleteEdges}\left(H, \{\operatorname{Sym2.mk}\left(s, u\right)\}\right), G\right)), \forall (x : \operatorname{Fin}\left(m\right)), \forall (y : \operatorname{Fin}\left(m\right)), (\left(\neg x \in \operatorname{range}\left(f\right)\right) \land \left(\left(\neg y \in \operatorname{range}\left(f\right)\right) \land \left(x \ne y \land \left(\operatorname{Adj}\left(G, f\left(s\right), x\right) \land \operatorname{Adj}\left(G, f\left(t\right), y\right)\right)\right)\right)) \Rightarrow \operatorname{Reachable}\left(\operatorname{induce}\left(G, \operatorname{Fin}\left(m\right) \setminus \operatorname{range}\left(f\right)\right), x, y\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim` (`✓ std3`).

*Citation.* Vladimir Gurvich; Matjaž Krnc; Martin Milanič; Mikhail Vyalyi (2026). *Non-induced inherent graphs*. DOI: [10.48550/arXiv.2611.06636](https://doi.org/10.48550/arXiv.2611.06636). URL: <https://arxiv.org/abs/2611.06636v1>.

*Commentary.*

The graphs are finite and simple. The roots are ordered and distinct, with the degree of the first at most the degree of the second. The first root has exactly one neighbor, u. Deleting the unordered edge between s and u keeps both roots and every vertex.

A copy is an injective adjacency-preserving map. The host may have extra edges between its image vertices. An extension attaches two distinct vertices outside the entire image to the respective roots. Reachability takes place in the induced graph on the complement of that image. The endpoints in the formula denote the corresponding vertices of this induced graph. A copy with no extensions is avoidable. Inherence asks for one avoidable copy in every finite host that contains a copy. Finite labels include every finite order and permit disconnected hosts.

**Theorem 1.2 (The four-arm tree confines the deleted path).**

$$\neg (\forall (n : \mathbb{N}), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (s : \operatorname{Fin}\left(n\right)), \forall (t : \operatorname{Fin}\left(n\right)), \forall (u : \operatorname{Fin}\left(n\right)), (\operatorname{degree}\left(H, s\right) \le \operatorname{degree}\left(H, t\right)) \Rightarrow \left((s \ne t) \Rightarrow \left((\forall (v : \operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(H, s, v\right) \Leftrightarrow v = u) \Rightarrow \left((\forall (m : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\operatorname{Nonempty}\left(\operatorname{Copy}\left(H, G\right)\right)) \Rightarrow \exists (f : \operatorname{Copy}\left(H, G\right)), \forall (x : \operatorname{Fin}\left(m\right)), \forall (y : \operatorname{Fin}\left(m\right)), (\left(\neg x \in \operatorname{range}\left(f\right)\right) \land \left(\left(\neg y \in \operatorname{range}\left(f\right)\right) \land \left(x \ne y \land \left(\operatorname{Adj}\left(G, f\left(s\right), x\right) \land \operatorname{Adj}\left(G, f\left(t\right), y\right)\right)\right)\right)) \Rightarrow \operatorname{Reachable}\left(\operatorname{induce}\left(G, \operatorname{Fin}\left(m\right) \setminus \operatorname{range}\left(f\right)\right), x, y\right)) \Rightarrow \forall (m : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\operatorname{Nonempty}\left(\operatorname{Copy}\left(\operatorname{deleteEdges}\left(H, \{\operatorname{Sym2.mk}\left(s, u\right)\}\right), G\right)\right)) \Rightarrow \exists (f : \operatorname{Copy}\left(\operatorname{deleteEdges}\left(H, \{\operatorname{Sym2.mk}\left(s, u\right)\}\right), G\right)), \forall (x : \operatorname{Fin}\left(m\right)), \forall (y : \operatorname{Fin}\left(m\right)), (\left(\neg x \in \operatorname{range}\left(f\right)\right) \land \left(\left(\neg y \in \operatorname{range}\left(f\right)\right) \land \left(x \ne y \land \left(\operatorname{Adj}\left(G, f\left(s\right), x\right) \land \operatorname{Adj}\left(G, f\left(t\right), y\right)\right)\right)\right)) \Rightarrow \operatorname{Reachable}\left(\operatorname{induce}\left(G, \operatorname{Fin}\left(m\right) \setminus \operatorname{range}\left(f\right)\right), x, y\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gurvich-krnc-milanic-vyalyi-2026-leaf-root-edge-deletion` (refuted) by `D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gurvich-krnc-milanic-vyalyi-2026-leaf-root-edge-deletion","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Martin Milanič; Mikhail Vyalyi (2026). *Non-induced inherent graphs*. DOI: [10.48550/arXiv.2611.06636](https://doi.org/10.48550/arXiv.2611.06636). URL: <https://arxiv.org/abs/2611.06636v1>.

*Commentary.*

Take the path on vertices 0 through 5 in order. Its roots are 0 and 3, of degrees one and two. For the intact path, work in the connected component of any containing copy. The specialization of Lemma 3.4 chooses a maximal connected vertex set disjoint from some copy. Path shifts and reroutings give either a copy with no extension or a copy whose exterior neighbors at both roots lie in that connected set. In the latter case the set supplies a walk between the endpoints of every extension. Transporting the copy and the walks to the original host proves inherence.

Delete edge 0–1. The host tree has center 0 and arms (0,1,2), (0,3,4), (0,5,6) and (0,7,8). The tuple (5,2,1,0,3,4) gives a copy of the deleted graph in pattern vertex order. In every copy the surviving four-edge path uses two full arms and places root 3 at the center. Root 0 lies on a third arm. Attach its other vertex at the first root and the midpoint of the fourth arm at the second root. The first endpoint is isolated in the graph induced outside the copy, so the two endpoints cannot be joined there. This applies to every copy of the deleted graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result`
