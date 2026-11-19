# An oriented lift of an alternating weld

## Abstract

Uniform undirected weld completions and their orientations.

**Theorem 1.1 (The conditional law given the orientation of the observed edges).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw.alternating_weld_orientation_law`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw.alternating_weld_orientation_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prescribed simple graph F on a finite vertex set of at least three vertices with two colors. Assume F extends to an alternating undirected full cycle. The uniform law on alternating oriented lifts projects to the uniform law on the undirected completions of F.

In each lift the prescribed orientation has as many directed edges as F has undirected edges. Given a prescribed orientation of positive mass, the directed full cycle is uniform over the alternating cycles extending that orientation. Its inclusion into the original lift space retains the prescribed orientation and the full successor permutation.

First use the uniform law on all undirected completions and their lifts. Alternation of the permutation is equivalent to alternation of its undirected graph, so restricting both laws to that event preserves the projection. Each directed prescribed edge projects to one undirected edge of F, and the lift gives each such edge exactly one direction. The fiber over a prescribed orientation is in bijection with the directed alternating completion space. Uniformity on that fiber gives the conditional law.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw.alternating_weld_orientation_law`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw](AlternatingUndirectedCompletionLaw.md)
