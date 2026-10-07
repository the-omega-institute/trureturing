# Derived Hom Filtration

## Abstract

Copyright (c) 2026. Released under the Apache 2.0 license. Extension of the literal generator comparison to every unbounded DSolid source. The inputs are the actual kernel resolution, finite lower layers, and the two actual truncation telescopes. No generation, replacement, derived full faithfulness, or derived adjunction is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1. This file is a proof attempt until a matching compiler/audit receipt exists.

**Theorem 1.1 (derived Inclusion map bijective).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusion_map_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusion_map_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal protected derived inclusion is bijective on morphisms from EVERY unbounded source to EVERY unbounded target. The proof uses the constructed generator resolution and both actual telescopes.

**Definition 1.2 (derived Inclusion Fully Faithful).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusionFullyFaithful`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusionFullyFaithful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual full-faithfulness data, with inverse induced by the proved literal-map bijection. No full-faithfulness premise is introduced.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusionFullyFaithful`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusion_map_bijective`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/DerivedGeneratorSums](DerivedGeneratorSums.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/DerivedHomTriangle](DerivedHomTriangle.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/LowerTruncationLayers](LowerTruncationLayers.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation](SolidGeneratorAugmentation.md)
