# A Path Hull Without Cut Vertices

## Abstract

Vertex inseparability produces a connected subgraph without cut vertices.

**Theorem 1.1 (A common cover for an unseparated set).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull.exists_no_cut_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull.exists_no_cut_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a connected simple graph and S a nonempty set of vertices. Suppose that for every deleted vertex z, every two members of S different from z remain mutually reachable in G-z. There exists a connected subgraph H containing the entire set S such that deleting any vertex from H leaves no pair of mutually unreachable remaining vertices. No finiteness or lower bound on the order is needed.

Take every vertex on any simple path with both endpoints in S, and induce a subgraph on this union. The trivial paths include S. If a vertex x in the union differs from a deleted vertex z, at least one of the two segments from x to its path endpoints avoids z, because the path has no repeated vertex. Thus x can reach a surviving endpoint in S. The hypothesis connects any two surviving endpoints after deletion, and a simple path between them is itself included in the union. Concatenating these paths proves the required reachability. For a singleton S, the union is a singleton; deleting its sole vertex leaves no pair to disconnect.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull.exists_no_cut_cover`
- Dependency: [D5/S3/Combinatorics/Graph/Eccentric/DePatraBridge](DePatraBridge.md)
