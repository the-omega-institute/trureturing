# Postorder

## Abstract

DFS postorder and cycles

**Theorem 1.1 (DFS postorder and cycles).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder.post_spec`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder.post_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

For every DFS forest, postorder is duplicate-free and has exactly the forest support as members. An edge from an earlier to a later output vertex has a return path. No acyclicity is assumed. If no emitted vertex lies on a nonempty full-graph cycle, emitted dependencies precede their sources. With an empty initial visited set, acyclicity of the subgraph induced by emitted vertices suffices.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
