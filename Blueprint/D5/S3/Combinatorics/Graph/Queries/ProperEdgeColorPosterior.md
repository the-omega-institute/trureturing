# A path and a cycle with the same uncolored record

## Abstract

A uniform proper edge coloring changes the graph posterior even with identical erased replies.

**Theorem 1.1 (The colored record favors the cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.proper_edge_colors_change_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.proper_edge_colors_change_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give the path 0–1–2–3 and the cycle 0–1–2–3–0 equal prior masses. After choosing the graph, uniformly choose one of its proper edge colorings with three colors and query the complete neighbor replies at vertices 1 and 2.

Those two vertices have identical uncolored replies in both graphs. Prescribe color 0 on edges 01 and 23 and color 1 on edge 12. The path has one matching coloring among twelve, and the cycle has two matching colorings among eighteen. The posterior probability of the cycle after observing the colored record is four sevenths.

The kernel enumerates assignments on the actual edge sets. The two matching cycle assignments differ in the color of edge 30, which only needs to avoid the common color 0 on its two adjacent edges.

**Theorem 1.2 (Erased replies do not determine the colored likelihood).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDoNotDetermineColorLikelihood`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDoNotDetermineColorLikelihood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the four labeled vertices, equality of the complete uncolored replies at vertices 1 and 2 does not determine the likelihood of the selected colored record. The path and cycle realize both erased replies and have positive numbers of proper colorings. Their respective likelihoods are one twelfth and one ninth.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDoNotDetermineColorLikelihood`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.proper_edge_colors_change_posterior`
