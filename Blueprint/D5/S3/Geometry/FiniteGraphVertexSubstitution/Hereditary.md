# Hereditary graph substitution

## Abstract

The actual mixed graph stages and original hereditary substitution induction.

**Definition 1.1 (The actual mixed replacement family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiber`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

At a vertex in the replaced finset use its final fiber D(v); elsewhere use PUnit in the same fiber universe. This family retains all previously replaced fibers on every restricted current link.

**Definition 1.2 (Finiteness of the mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberFintype`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Each mixed fiber is finite by its selected finite final-fiber or singleton branch.

**Definition 1.3 (Decidable equality of the mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberDecidableEq`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Branch reduction transfers decidable equality from each final fiber or from the singleton.

**Definition 1.4 (Nonempty mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberNonempty`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

If every final fiber is nonempty, both branches of every mixed fiber are nonempty. This supplies actual current-link vertices when the restricted base is nonempty.

**Definition 1.5 (Graphs on the mixed family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageGraphs`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageGraphs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Transport H(v) across the selected branch equality, and transport the edge-free singleton graph across the other branch equality. These are graphs on the actual dependent stage types.

**Definition 1.6 (The initial stage is the base graph).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.initialStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.initialStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The stage with no replaced vertices is isomorphic to the base graph, by fiberwise singleton transport and projection. This starts replacement induction without an order-two assumption.

**Definition 1.7 (The final stage is full substitution).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.finalStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.finalStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The stage indexed by the full base finset is isomorphic to the full original heterogeneous substitution, by the explicit selected-fiber equivalences.

**Definition 1.8 (A supplier replacement is the next mixed stage).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.replacementStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.replacementStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Pointwise branch casts identify the supplier newFiber construction at v with the stage indexed by insert v R, preserving actual fiber adjacency. When v is absent from R, the old stage fiber at v is a singleton; no singleton assumption is made on the new final fiber. These transports serve the original private hereditarySubstitutionCore, with strong induction on base cardinality and inner induction on replaced vertices. The link carries all current mixed fibers. A nonempty link uses the smaller-base induction; an empty link uses the augmented simplicial unit. The core is consumed directly by HereditaryLexicographicProduct with the class of actual finite positive sphere-bouquet models. There its point and homotopy inputs are constructed, and its finite native ordinary-join and selected-coordinate-vertex wedge inputs are discharged by the actual FiniteComponentClosure constructions. No second graph induction is introduced. The original core alone remains conditional on its explicit class-closure inputs.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.finalStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.initialStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.replacementStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiber`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberDecidableEq`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberFintype`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageFiberNonempty`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.stageGraphs`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](../FiniteGraphVertexSubstitution.md)
