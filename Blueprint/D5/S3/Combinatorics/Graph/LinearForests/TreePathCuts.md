# Path cuts in trees

## Abstract

The components left by a cut on one path of a tree form a path of components.

**Theorem 1.1 (The residual component graph is a path).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall C \in \operatorname{Set}\left(\operatorname{Sym2}\left(V\right)\right),\; (\operatorname{IsTree}\left(G\right) \land \operatorname{OnSpine}\left(G, C\right)) \Rightarrow (\exists n \in Nat,\; \operatorname{Nonempty}\left(\operatorname{GraphIso}\left(\operatorname{pathGraph}\left(n + 1\right), \operatorname{componentGraph}\left(G, C\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts.componentGraph_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OnSpine(G,C) means that one simple walk of G contains every edge of C. Contract each connected component of G after deleting C. Adjacencies of the component graph are original cut edges between their components.

Every cut edge separates its endpoints and is unique between its two residual components. Project the original walk by keeping the cut edges. Its projection is a trail in an acyclic component graph, so it is a simple walk. Connectedness and closure under adjacency imply that its support contains every component. For the empty cut the quotient has one vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts.componentGraph_path`
