# Every finite actual flag graph admits terminal leaf pruning

## Abstract

Every finite actual flag graph admits terminal leaf pruning

**Theorem 1.1 (A terminal chronology exists without a supplied pruning certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence.exists_leaf_pruning`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence.exists_leaf_pruning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite cyclic flag graph there exists a genuine LeafPruning: every deleted owner orbit has at most one remaining actual incident flag at deletion time, numbered anchor vertices are protected, and every terminal nonanchor orbit has at least two remaining flags. The theorem assumes neither connectedness nor stability and retains loops and parallel edges. Its proof starts with the empty chronology, bounds deletion length by the number of actual owner orbits, and chooses a longest admissible prefix. Any terminal nonanchor with at most one remaining flag would extend that prefix by one step, contradicting maximality. Both flags of a loop are counted, so a loop cannot be discarded as a degree-one adjacency. Together with the existing extraction and vanishing theorems, this supplies actual terminal prunings for later arguments; uniqueness of the retained core, the bare-circle source case, global skeleton normal form and the full four-loop theorem are separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningExistence.exists_leaf_pruning`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/FlagPruning](FlagPruning.md)
