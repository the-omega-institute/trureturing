# ForestInvariant

## Abstract

Final visited set

**Theorem 1.1 (Final visited set).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.union`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.union` (`✓ std3`). ∎

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

The final visited set is the union of the initial visited set and forest support.

**Theorem 1.2 (Fresh forest vertices).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.inter`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.inter` (`✓ std3`). ∎

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

The initial visited set is disjoint from forest support.

**Theorem 1.3 (Forest vertices are reachable).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.sound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.sound` (`✓ std3`). ∎

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

Every forest vertex is reachable from a forest root.

**Theorem 1.4 (Forest successors are visited).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.succSet_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.succSet_support_subset` (`✓ std3`). ∎

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

Every successor of a forest vertex belongs to the final visited set. Generic Mathlib closure preservation extends this to paths when successors of initially visited vertices are also finally visited; no separate completeness wrapper is retained.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
