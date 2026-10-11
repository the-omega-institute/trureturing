# Components and Vertex Cuts

## Abstract

A finite connected graph separated by one vertex splits into two connected pieces sharing that vertex.

Induce(G,S) is the induced graph on the vertex subset S. Component(H,v) denotes the connected component of v in H, and Reachable(H,u,v) means that H contains a finite walk between the two vertices. Connectedness includes a nonempty vertex type. Accordingly, a disconnected induced graph supplies two unreachable vertices only when its vertex set is also known to be nonempty.

**Theorem 1.1 (Two Connected Sides of a Cut Vertex).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall x \in V,\; \forall d \in V,\; \forall e \in V,\; (\mathrm{Connected}\left(G\right) \land \left(d \ne x \land \left(e \ne x \land \neg (\mathrm{Reachable}\left(\mathrm{Induce}\left(G, \mathrm{Compl}\left(\mathrm{Singleton}\left(x\right)\right)\right), d, e\right))\right)\right)) \Rightarrow (\exists A \in \mathrm{Finset}\left(V\right),\; \exists B \in \mathrm{Finset}\left(V\right),\; \mathrm{Nonempty}\left(A\right) \land \left(\mathrm{Nonempty}\left(B\right) \land \left(\neg (\mathrm{Mem}\left(x, A\right)) \land \left(\neg (\mathrm{Mem}\left(x, B\right)) \land \left(\mathrm{Disjoint}\left(A, B\right) \land \left(\mathrm{Insert}\left(x, \mathrm{Union}\left(A, B\right)\right) = \mathrm{Univ}\left(V\right) \land \left(\left(\forall u \in V,\; \forall w \in V,\; (\mathrm{Mem}\left(u, A\right) \land \mathrm{Mem}\left(w, B\right)) \Rightarrow (\neg (\mathrm{Adj}\left(G, u, w\right)))\right) \land \left(\mathrm{Connected}\left(\mathrm{Induce}\left(G, \mathrm{Insert}\left(x, A\right)\right)\right) \land \mathrm{Connected}\left(\mathrm{Induce}\left(G, \mathrm{Insert}\left(x, B\right)\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Cuts.cut_partition_of_unreachable` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Let G be connected on a finite vertex type with decidable equality. Suppose d and e both differ from x and are unreachable from one another after deleting x. There are disjoint nonempty finite sets A and B, both omitting x, that partition all other vertices. No edge runs between A and B, and each induced graph on A with x adjoined and on B with x adjoined is connected. One side can be chosen as the component of e after deletion; every remaining component attaches to x and belongs to the other side. The two unreachable vertices ensure that neither side is empty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Cuts.cut_partition_of_unreachable`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Coloring](Coloring.md)
