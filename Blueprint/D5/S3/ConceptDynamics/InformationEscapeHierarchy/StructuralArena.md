# Structural Arenas

## Abstract

Arbitrary state carriers support structural theorem catalogs, with finite catalogs embedded canonically.

**Definition 1.1 (Structural arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A structural arena carries an arbitrary state type and imposes no finiteness or decidable-equality requirement.

**Definition 1.2 (Structural kernel).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A structural kernel packages a binary relation together with its equivalence proof.

**Definition 1.3 (Forget kernel decidability).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.ofDecidableKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.ofDecidableKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite kernel relation and equivalence proof are retained definitionally while its decision procedure is forgotten.

**Definition 1.4 (Structural theorem unit).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralTheoremUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralTheoremUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A proved statement carries a finite family of primitive structural kernels on the arena state type.

**Definition 1.5 (Structural catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A structural catalog is a finite decidable family of structural theorem units.

**Definition 1.6 (Finite arena embedding).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding forgets finite enumeration and decidable equality while preserving the state carrier.

**Definition 1.7 (Finite theorem-unit embedding).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralTheoremUnit`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralTheoremUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every primitive kernel is embedded by forgetting only its decision procedure, and the statement proof is retained.

**Definition 1.8 (Finite catalog embedding).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite catalog index and theorem lookup are retained while each theorem unit is structurally embedded.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.StructuralTheoremUnit`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.ofDecidableKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.toStructuralTheoremUnit`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
