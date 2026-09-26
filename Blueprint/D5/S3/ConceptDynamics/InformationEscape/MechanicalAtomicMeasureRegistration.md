# MechanicalAtomicMeasureRegistration

## Abstract

The atomic measure is compared with its mass, distribution, hit, and support targets on complete admissible parameter families.

**Definition 1.1 (Mass parameters).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassInput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input stores a real ratio and phase; the target law checks the admissible range.

**Definition 1.2 (Mass readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate is total mass and the second is mass on the positive unit interval.

**Definition 1.3 (Mass target).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massTarget`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both coordinates equal one on admissible parameters; elsewhere the target equals the measured readout.

**Definition 1.4 (Mass family).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each readout retains its value on every admissible mass input.

**Definition 1.5 (Distribution parameters).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionInput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input stores a real ratio, threshold, and phase; the target law checks their admissible ranges.

**Definition 1.6 (Distribution readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The geometric atomic measure is evaluated on the interval below the threshold.

**Definition 1.7 (Distribution target).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionTarget`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On admissible parameters the target is the completed mechanical readout; elsewhere it equals the measured distribution.

**Definition 1.8 (Distribution family).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is a function on all admissible distribution parameters.

**Definition 1.9 (Singleton parameters).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitInput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input stores a real ratio, phase, and threshold; the target law checks the phase and interior threshold conditions.

**Definition 1.10 (Singleton mass).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The atomic measure is evaluated at the singleton threshold.

**Definition 1.11 (Integer-hit series).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitTarget`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On admissible parameters each integer-hit time contributes its coefficient; elsewhere the target equals singleton mass.

**Definition 1.12 (Singleton family).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singleton law retains all admissible ratios, phases, and thresholds.

**Definition 1.13 (Support parameters).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportInput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input stores a real ratio and phase; the target law checks their admissible ranges.

**Definition 1.14 (Measured support).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the topological support of the geometric atomic measure.

**Definition 1.15 (Support target).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportTarget`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target is the closed unit interval on admissible parameters and the measured support elsewhere.

**Definition 1.16 (Support family).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support comparison retains every admissible ratio and phase.

**Definition 1.17 (Mass comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT role reads the complete mass function; the law equates it with the target on every parameter.

**Definition 1.18 (Distribution comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT role reads the atomic distribution function; the law equates it with the completed mechanical readout.

**Definition 1.19 (Singleton comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT role reads singleton mass; the law equates it with the integer-hit series.

**Definition 1.20 (Support comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT role reads the support function; the law equates it with the closed-interval target.

**Definition 1.21 (Mass realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected readout is the measured mass pair at each ratio and phase.

**Definition 1.22 (Distribution realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected readout is the atomic distribution at each ratio, threshold, and phase.

**Definition 1.23 (Singleton realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected readout is singleton mass at each ratio, phase, and threshold.

**Definition 1.24 (Support realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected readout is measured support at each ratio and phase.

**Definition 1.25 (Complete readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.JumpOutput`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.JumpOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output records the completed mechanical readout at every ratio, slope, and phase.

**Definition 1.26 (Selected readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected function is the completed mechanical readout.

**Definition 1.27 (Rational jump law).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.rationalJumpArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.rationalJumpArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At reduced rational slopes and zero phase, the CUT function has the stated geometric jump.

**Definition 1.28 (Readout realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization uses the completed mechanical readout in the rational jump law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionInput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.DistributionOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitInput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.HitOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.JumpOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassInput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.MassOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportInput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.SupportOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.distributionTarget`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.hitTarget`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.jumpRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.massTarget`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.rationalJumpArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration.supportTarget`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure](../../../S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration](MechanicalDyadicRegistration.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/MechanicalReadoutSources](MechanicalReadoutSources.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ObjectDomainArena](ObjectDomainArena.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates](PointwiseRegistrationTemplates.md)
