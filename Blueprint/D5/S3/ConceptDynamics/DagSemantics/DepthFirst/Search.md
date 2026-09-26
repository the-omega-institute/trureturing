# Search

## Abstract

Depth-first forest construction

**Definition 1.1 (Depth-first forest construction).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Search.dfsForest`

*Formalization.* `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Search.dfsForest` (`✓ std3`).

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

The algorithm marks a fresh vertex before descending, threads the child traversal's visited set into sibling traversal, and returns the original forest and final visited dictionary. The retained original proofs roots_dfsForest'_fst_subset, subset_visited_dfsForest'_snd and isDFSForest_dfsForest' establish its DFS invariant and supplied-root coverage. Their primed names are preserved.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
