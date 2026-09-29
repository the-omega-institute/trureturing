# MechanicalPhaseAverageRegistration

## Abstract

The atomic phase average and volume are functions on the same admissible inputs.

**Definition 1.1 (Admissible input).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.PhaseAverageInput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.PhaseAverageInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An input contains a ratio strictly between zero and one and a measurable real set contained in the unit interval.

**Definition 1.2 (Phase average).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageIntegral`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first function integrates the geometric atomic measure over half-open phases.

**Definition 1.3 (Volume).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageVolume`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageVolume` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second function assigns the volume of the same target set.

**Definition 1.4 (Readout comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two CUT roles compare the full functions on admissible inputs. The source object domain is the type of real sets; finite readout states only select the roles.

**Definition 1.5 (Selected readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected realization reads the phase-average and volume functions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.PhaseAverageInput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageIntegral`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration.phaseAverageVolume`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure](../../../S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/MechanicalReadoutSources](MechanicalReadoutSources.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ObjectDomainArena](ObjectDomainArena.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
