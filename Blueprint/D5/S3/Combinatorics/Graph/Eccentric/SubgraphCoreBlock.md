# The Subgraph Core and Native Blocks

## Abstract

The entire maximizing set of actual connected-subgraph counts lies in one block.

Dinesh Pandey and Kamal Lochan Patra, Some new central parts of connected graphs, arXiv:2110.00738v1, https://arxiv.org/pdf/2110.00738v1, page 9, state: Conjecture 3.25. The subgraph core of a graph G is contained in a block of G. Definition 3.23 on that page counts connected subgraphs containing a vertex. Page 1 specifies finite simple connected undirected graphs, defines a cut vertex by disconnection after deletion, and defines a block as a maximal subgraph with no cut vertex.

**Definition 1.1 (Actual vertex and edge choices).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphNumber`

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite simple graph G and vertex v, subgraphNumber(G,v) is the cardinality of the actual connected subgraphs containing v. It uses countContaining(G,{v}) from DePatraBridge. Each subgraph has its own vertex set and edge set. Distinct edge choices are distinct objects, inducedness is not required, and singleton subgraphs are included.

**Definition 1.2 (The entire maximizing set).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphCore`

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex v belongs to subgraphCore(G) precisely when subgraphNumber(G,w) is at most subgraphNumber(G,v) for every vertex w of G.

**Definition 1.3 (Maximal connected subgraphs without a cut vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.NativeBlock`

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.NativeBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NoCut(H) means that H is connected and deleting any one vertex leaves no pair of mutually unreachable remaining vertices. Deletion restricts both the actual vertex set and the actual edges. NativeBlock(H) means maximality for NoCut under subgraph inclusion, including both vertices and edges. Empty deletion has no disconnected pair. Thus a one-vertex graph has its singleton block, and a bridge edge is admitted as a block. No order cutoff is imposed.

**Theorem 1.4 (One block contains all maximizers).**

Lean statement: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result` (`✓ std3`). ∎

*Resolves.* `Problems/pandey-patra-2021-subgraph-core` (proved) by `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pandey-patra-2021-subgraph-core","declaration_gid":"D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result","resolution_kind":"proved"} -->

*Citation.* Dinesh Pandey; Kamal Lochan Patra (2021). *Some new central parts of connected graphs*. URL: <https://arxiv.org/abs/2110.00738v1>.

*Commentary.*

For every finite vertex type V and every connected simple graph G on V, there exists a native block B of G with subgraphCore(G) contained in B.verts. The block is shared by the entire maximizing set.

The counting argument extends a connected subgraph H containing x and omitting r along a path from r to x, stopping at its first encounter with H. Let L be the path before that encounter and K the union of the path with H. Then K contains r and x, L contains r and omits x, and deleting L's vertices from K recovers H, including its edge choices. This injects the x-only subgraphs into pairs consisting of an r-and-x subgraph and an r-only subgraph. Writing d for the former count and a for all r-containing subgraphs gives the bound c <= d(a-d) for the x-only count c.

At a one-vertex separation with root r, write a and b for the local root counts on the two sides, and d and e for the local joint counts at r,x and r,y. Exact gluing gives f(r)=ab, f(x)=c+db and f(y)=h+ea. The path-extension bound gives c <= d(a-d) and h <= e(b-e). The root singletons give d<a and e<b. If both f(x) and f(y) were at least f(r), these inequalities would force b<=d<a<=e<b, a contradiction. Hence maximizers different from r cannot lie in different components after deleting r.

For a maximizing set with at least two vertices, take the union of all simple paths between maximizing vertices. Every vertex on such a path, after deleting a vertex z, can still reach one endpoint different from z along that path. All maximizing vertices different from z are mutually reachable after deleting z by the separation argument, and their connecting simple paths belong to the same union. The induced graph on this union therefore has no cut vertex. A singleton maximizing set starts with its singleton subgraph. Finiteness extends either subgraph to a maximal one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.NativeBlock`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphCore`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.subgraphNumber`
- Dependency: [D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting](DePatraCounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull](SubgraphCoreHull.md)
