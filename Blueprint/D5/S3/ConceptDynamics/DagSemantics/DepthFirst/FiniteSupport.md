# FiniteSupport

## Abstract

Dependent finite support

**Definition 1.1 (Dependent finite support).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/FiniteSupport.support`

*Formalization.* `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/FiniteSupport.support` (`✓ std3`).

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

The original finite support construction collects keys whose function values differ from their designated defaults. Its consumer uses the pinned Mathlib membership theorem directly through the original record fields.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
