# Engine Census Self-Application

## Abstract

The escape engine characterizes its own census on a two-stage arena.

**Definition 1.1 (Stage type).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.Stage`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.Stage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite meta-arena has a before and an after stage.

**Definition 1.2 (Census arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The engine census ranges over the two Boolean states.

**Definition 1.3 (Stage-indexed catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its lone CUT is constant before separation and identity afterward.

**Definition 1.4 (SYSTEM readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the canonical leave-one-out unique-capture count.

**Definition 1.5 (Engine characterization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemCharacterization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemCharacterization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every stage specializes the canonical exact-rate criterion.

**Definition 1.6 (Primitive-law Stage arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.arena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.arena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT slot reads a natural-valued engine census at each stage.

**Definition 1.7 (Census realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization calls the catalog's unique-capture census directly.

**Definition 1.8 (SYSTEM statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law joins readout identity, exact-rate characterization, and true-stage irredundancy.

**Theorem 1.9 (The engine census self-applies).**

$$(\forall stage: Stage,\\readout\left(systemRealization, 0, stage\right) = uniqueCaptureCount\left(censusCatalog\left(stage\right), 0\right)) \land\\(\forall stage: Stage,\\LowersEscape\left(censusCatalog\left(stage\right), 0\right) \iff 0 < uniqueCaptureCount\left(censusCatalog\left(stage\right), 0\right)) \land\\CatalogIrredundant\left(censusCatalog\left(true\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.engine_census_self_application` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical exact-rate theorem proves the characterization; the stage census changes from zero to two.

**Theorem 1.10 (Self-application realization certificate).**

$$LegacyPrimitiveRealization\left(arena, SystemStatement, systemRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.system_self_application_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The SYSTEM theorem uses the same legacy registration interface as the ten frozen applications.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.Stage`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemCharacterization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.SystemStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.arena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.censusCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.engine_census_self_application`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.systemRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.system_self_application_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/Laws](Laws.md)
