# Registration Shadows

## Abstract

Ten shadow registrations compare generated realizations with their hand registrations on canonical arenas.

Each shadow retains unrestricted agreement-kernel equality, statement equality, nondegeneracy, a complete state enumeration, a law-sensitivity witness, and a separated state pair. The module seals the ten registrations and checks their finite-occurrence census queries.

**Definition 1.1 (Spectrum shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bijection helper uses SpectrumAtom.index on the canonical spectrum arena.

**Theorem 1.2 (Spectrum agreement kernels coincide).**

$$\forall x y, \operatorname{agrees}(shadow, x, y) \iff \operatorname{agrees}(hand, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrum_kernel_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here shadow denotes spectrumRealization.toPrimitiveBundle and hand denotes FirstThreeRealizations.spectrumRealization.toPrimitiveBundle. The equivalence holds for every pair of states.

**Definition 1.3 (Intervention shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.interventionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.interventionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The separation template supplies intervention and counterfactual readouts on the canonical intervention arena.

**Definition 1.4 (Observation shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.observationRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.observationRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same separation template supplies observation and intervention readouts on the canonical observation-intervention arena.

**Definition 1.5 (Agenda shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.agendaRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.agendaRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The admitted-surjection helper uses the sequential winner and agenda validity predicate.

**Definition 1.6 (Preemption shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.preemptionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.preemptionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchored-separation helper uses end state, active cause, ordered-preemption predicates, and the two source traces.

**Definition 1.7 (Context shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.contextRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.contextRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The context-selection helper uses the source interpretation parameters and its two fixed-meaning predicates.

**Definition 1.8 (Static-design shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.staticRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.staticRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact-design helper supplies the two Boolean readouts over Fin 3.

**Definition 1.9 (Completion shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.completionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.completionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The completion-exchange helper uses the source counterexample transitions and readout.

**Definition 1.10 (Gluing shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.gluingRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.gluingRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scope-table helper supplies the three local equality and inequality predicates.

**Definition 1.11 (Adaptive residue shadow).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-step helper supplies residueReadout on the canonical residueArena.

**Theorem 1.12 (Adaptive residue registration bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic twoStepLegacy bridge preserves the full source statement, including history-dependent questions and minimum costs.

**Theorem 1.13 (Residue agreement kernels coincide).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_kernel_equal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_kernel_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of states, the generated bundle agrees exactly when the hand bundle agrees.

**Theorem 1.14 (Nondegenerate residue arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical arena contains distinct states.

**Definition 1.15 (Complete residue enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shadow uses the canonical arena's complete state enumeration.

**Theorem 1.16 (Residue law sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_lawSensitive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_lawSensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source realization satisfies the law; the constant-false sensor family does not.

The library contains one reused template, separation, and eight single-consumer helpers. The two-step helper transports Nat.find minima and preserves the higher-order binary protocol law. All ten shadows participate in the shared seal and certified finite-occurrence census queries.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.agendaRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.completionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.contextRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.gluingRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.interventionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.observationRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.preemptionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residueRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_kernel_equal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_lawSensitive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.residue_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrum_kernel_equal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.staticRealization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](RegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeCounting/Enumerations](../InformationEscapeCounting/Enumerations.md)
