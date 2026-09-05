# Local-Law Gluing Obstruction Arena

## Abstract

The three-cycle gluing obstruction is expressed by three coded admission tests.

**Definition 1.1 (Adjacent equality law).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.sameLaw`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.sameLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equality relation supplies each of the two adjacent local laws.

**Definition 1.2 (Outer inequality law).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.differentLaw`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.differentLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inequality relation supplies the outer local law that obstructs global gluing.

**Definition 1.3 (Gluing readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.GluingReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.GluingReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite index type names the three coded ADMIT readouts.

**Definition 1.4 (Decidable equality for gluing readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instDecidableEqGluingReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instDecidableEqGluingReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.5 (Finite gluing readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instFintypeGluingReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instFintypeGluingReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.6 (Typed gluing signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature assigns Boolean outputs and the ADMIT axis to all three readout indices.

**Definition 1.7 (Frozen gluing statement type).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.LocalLawGluingStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.LocalLawGluingStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state.

**Definition 1.8 (Local-law gluing arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law compares existential fibers of the three realization ADMIT slots and rejects a jointly admitted triple.

**Theorem 1.9 (Local-law gluing arena is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(localLawGluingArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite arena has at least two distinct attempted global states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.GluingReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.LocalLawGluingStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.differentLaw`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instDecidableEqGluingReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.instFintypeGluingReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.localLawGluingSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.sameLaw`
- Dependency: [D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction](../Gluing/LocalLawGluingObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
