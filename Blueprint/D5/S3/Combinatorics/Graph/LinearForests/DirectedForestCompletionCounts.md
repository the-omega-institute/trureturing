# Counts for directed linear-forest completions

## Abstract

Exact counts on a directed forest and its full-cycle completion event.

**Theorem 1.1 (Edges and uniform full-cycle extension mass).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts.edge_and_completion_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts.edge_and_completion_mass` (`✓ std3`). ∎

*Citation.* Boaz Tsaban (2003). *Permutation graphs, fast forward permutations, and sampling the cycle structure of a permutation*. DOI: [10.1016/S0196-6774(03)00017-8](https://doi.org/10.1016/S0196-6774(03)00017-8).

*Commentary.*

Let an acyclic relation on N labelled vertices have at most one incoming and one outgoing edge per vertex. Include the isolates in its c weak components and assume N and c are at least two. The edge set has N minus c members. For any uniform probability mass on the actual full cycles, the event of extending all the prescribed edges has positive mass equal to (c-1)! divided by (N-1)!.

Projecting each edge to its source gives a bijection onto the vertices with an outgoing edge. Their complement consists of the component tails. The completion equivalence counts the extension event, and every full cycle has the same mass. Summing over that event gives the stated ratio.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts.edge_and_completion_mass`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion](DirectedForestCompletion.md)
