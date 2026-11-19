# Alternating undirected cycle completions

## Abstract

The extension event and conditional probability on actual alternating undirected cycles.

**Theorem 1.1 (Fixed-edge conditioning under the uniform alternating undirected cycle law).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw.alternating_undirected_completion_law`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw.alternating_undirected_completion_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Catherine Greenhill; Svante Janson; Jeong Han Kim; Nicholas C. Wormald (2002). *Permutation pseudographs and contiguity*. DOI: [10.1017/S0963548301005065](https://doi.org/10.1017/S0963548301005065).

*Commentary.*

A finite labelled vertex set has n vertices of each of two colors, with at least four vertices in total. An alternating completed graph is an undirected connected two-regular graph on these vertices whose edges have differently colored endpoints. The ambient carrier has n! (n−1)! / 2 such graphs.

Let F be any prescribed simple graph on the same vertices. The event that every edge of F is present consists of the alternating completed graphs extending F. Its uniform ambient probability is the number of those completions divided by the ambient count. The event has positive probability exactly when a completion exists. At positive probability, the uniform mass on those completions gives the conditioned law by inclusion into the ambient carrier.

A full-cycle successor permutation alternates precisely when its undirected shadow has cross-color edges. Restricting the shadow to alternating lifts therefore preserves its two-element fibers. The directed alternating count divided by two gives the ambient count. The inclusion of completed graphs identifies the fixed-edge law with uniform mass on the corresponding subset.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw.alternating_undirected_completion_law`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw](AlternatingCompletionLaw.md)
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw](UndirectedCycleCompletionLaw.md)
