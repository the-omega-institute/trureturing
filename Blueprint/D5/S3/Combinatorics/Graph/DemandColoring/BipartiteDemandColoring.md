# Exact demand allocation on a two-colored graph

## Abstract

A supplied total two-coloring permits exact natural demands to share a common finite palette.

**Theorem 1.1 (One palette with independent layers and exact multiplicities).**

Lean statement: `D5/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring.exists_independent_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring.exists_independent_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any type, G a simple graph on V, and b a proper total coloring of G by Bool. For every natural k and demand function z from V to the natural numbers, suppose z(v) is at most k for every vertex, and z(u)+z(v) is at most k for every edge uv. There exists one function W from Fin k to V to Bool such that for every palette index c the vertices with W(c,v)=true form a G-independent set, and for every v the number of indices c with W(c,v)=true is exactly z(v). No finiteness or decidable adjacency assumption is imposed on V or G. Isolated vertices use the vertex capacity. When k is zero every demand is zero and there are no layers.

Vertices colored true receive the initial segment c<z(v); vertices colored false receive the final segment k-z(v)<=c. An edge joins opposite colors, and its demand-sum bound makes these segments disjoint. Initial-segment counting and complement counting give the exact multiplicities in the same allocation. Repeated independent sets and empty layers are permitted. This is classical bipartite multicoloring by intervals, with the total coloring supplied as data.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring.exists_independent_layers`
