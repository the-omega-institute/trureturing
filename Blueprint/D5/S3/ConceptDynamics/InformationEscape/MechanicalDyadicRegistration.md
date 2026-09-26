# MechanicalDyadicRegistration

## Abstract

Dyadic mechanical boundary registrations retain the complete parameterized readouts.

**Definition 1.1 (mechanicalReadoutSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One Unit-indexed CUT slot returns a typed observation; there are no anchor slots.

**Definition 1.2 (mechanicalReadoutRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization returns its supplied observation function without reducing it to a theorem's truth value.

**Definition 1.3 (LowerOutput).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.LowerOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.LowerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A slope and precision select a lower dyadic slope and its boundary bit.

**Definition 1.4 (UpperOutput).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.UpperOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.UpperOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Slope, phase, precision, and position select an actual upper dyadic mechanical bit.

**Definition 1.5 (StableOutput).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.StableOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.StableOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Slope, phase, and position select both an integer floor and an actual mechanical bit.

**Definition 1.6 (lowerReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Floor division constructs the lower dyadic slope; the second component reads its mechanical bit at phase one minus the source slope.

**Definition 1.7 (upperReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ceiling division constructs the upper dyadic slope before reading the mechanical bit at the supplied phase and position.

**Definition 1.8 (stableReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same slope and phase supply the cumulative floor and the mechanical bit at the selected position.

**Definition 1.9 (lowerArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every irrational slope strictly between zero and one and every precision, the law retains the nonnegative lower slope, its positive error below the reciprocal power of two, the true source boundary bit, and the false lower bit.

**Definition 1.10 (upperArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each slope, phase, and finite word length, the law requires a precision after which every observed upper bit equals the source bit.

**Definition 1.11 (stableArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Without positive-time integer hits in the finite prefix, the law requires a positive slope radius preserving every listed floor and mechanical bit.

**Definition 1.12 (lowerRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected CUT readout is the complete lower dyadic slope and boundary-bit function.

**Definition 1.13 (upperRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected CUT readout is the complete upper dyadic bit function.

**Definition 1.14 (stableRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected CUT readout is the joint floor and mechanical-bit function.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.LowerOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.StableOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.UpperOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.lowerRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.mechanicalReadoutSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.stableRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.upperRealization`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](../../../S1/Words/Mechanical/MechanicalSlopeSensitivity.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ObjectDomainArena](ObjectDomainArena.md)
