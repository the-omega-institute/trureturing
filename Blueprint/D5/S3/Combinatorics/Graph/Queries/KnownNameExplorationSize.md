# The size of a known-name exploration

## Abstract

A degree bound controls the number of names seen during an exploration.

**Theorem 1.1 (Degree bound for a known-name exploration from a root).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize.known_names_card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize.known_names_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectively name the vertices of a simple graph in a finite name set. Initially give a deterministic strategy only the root's name. Query the graph for complete unordered neighborhoods at known names and answer all other queries with a synthetic miss. If the root has degree at most d and all vertices have degree at most d plus one, then the final number of known names is at most one plus d times the number of actual calls. A known vertex other than the root was revealed by a query to a neighbor whose name is still known.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize.known_names_card_bound`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation](KnownNameSimulation.md)
- Dependency: [D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory](NamedNeighborhoodHistory.md)
