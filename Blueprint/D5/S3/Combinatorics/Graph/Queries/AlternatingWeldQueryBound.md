# A fresh weld edge after complete queries

## Abstract

A one-step probability estimate for an alternating weld.

**Theorem 1.1 (The fresh-neighbor bound for a prescribed subgraph).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_neighbor_mass_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_neighbor_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite vertex set has at least three vertices and is split into two color classes of size n. Let F have at least one undirected alternating full-cycle completion and let f be its number of edges. If f plus two is at most n, there is a uniform law on its alternating completions. Under this law, the outer mass of an edge outside F from x to any vertex of a finite target set S is at most twice the size of S divided by n minus f minus one.

Condition on the orientation of the edges of F. The outgoing estimate in each orientation fiber is uniform in the fiber. Reversal then gives the same mass for the incoming event. Every fresh undirected edge belongs to their union.

**Theorem 1.2 (The conditional probability of a fresh weld edge to a target set).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_query_prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_query_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a uniform alternating full cycle join two sets of n leaves embedded in a fixed graph. Condition on a positive-mass transcript of q full unordered neighborhood queries. The reference cycle has edges disjoint from the fixed graph. For a leaf x and a finite target set S of leaves, if 2q + 2 is at most n, the conditional mass of a weld edge from x to S absent from the exposed weld is at most 2 times the size of S divided by n minus 2q minus one.

The transcript law gives a uniform completion of the exposed weld. Each query contributes at most two weld edges, so the exposed edge count is at most 2q. Orient the completion and condition on the orientation of the exposed edges. In each orientation fiber, a fresh outgoing edge joins the tail of one component to a head in another. Sending each target leaf to its component yields at most as many candidate components as leaves in S. The directed successor bound applies on each fiber. Averaging over the fibers, reversing direction and bounding the mass of the outgoing-or-incoming event gives the undirected estimate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_neighbor_mass_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_query_prefix_bound`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound](../LinearForests/AlternatingForestSuccessorBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw](../LinearForests/AlternatingWeldOrientationLaw.md)
- Dependency: [D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript](UnorderedWeldTranscript.md)
