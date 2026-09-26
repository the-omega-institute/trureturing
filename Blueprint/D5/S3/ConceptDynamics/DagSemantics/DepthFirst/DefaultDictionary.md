# DefaultDictionary

## Abstract

Finite dictionaries with a default

**Definition 1.1 (Finite dictionaries with a default).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary.DefaultDict`

*Formalization.* `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary.DefaultDict` (`✓ std3`).

*Citation.* Yuyang Zhao (2023). *Algorithm graph interfaces and verified depth-first search, revision ce7dc1da*. URL: <https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67>.

*Commentary.*

The original interface specifies total lookup, finite support, a default value and point updates. The retained Vector.WithDefault instance supplies arbitrary finite index arrays.

The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.
