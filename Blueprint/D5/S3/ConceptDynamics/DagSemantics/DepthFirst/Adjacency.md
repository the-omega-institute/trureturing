# Adjacency

## Abstract

Paths and relational reachability

**Theorem 1.1 (Paths and relational reachability).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Adjacency.reachable_eq_reflTransGen`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Adjacency.reachable_eq_reflTransGen` (`✓ std3`). ∎

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

Nonempty quiver paths, including the empty path, coincide with the reflexive transitive closure of adjacency.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
