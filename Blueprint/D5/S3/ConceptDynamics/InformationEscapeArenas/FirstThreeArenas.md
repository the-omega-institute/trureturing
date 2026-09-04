# First Three Information-Escape Arenas

## Abstract

Finite typed arenas for agenda power, adaptive residues, and spectrum atoms.

**Definition 1.1 (Agenda finite instance).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite instance obtained through a private equivalence.

**Definition 1.2 (Agenda readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.AgendaReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.AgendaReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type separates the sequential winner from agenda validity.

**Definition 1.3 (Agenda power signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed signature assigns a three-valued winner output and a Boolean validity output to the agenda carrier.

**Definition 1.4 (Agenda power arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena packages the finite Agenda state, agendaPowerSignature, and the realization law asserting all winners plus a separating valid pair.

**Definition 1.5 (Adaptive depth).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.adaptiveDepthFor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.adaptiveDepthFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The noncomputable depth helper selects the least exact adaptive depth when one exists and returns zero otherwise.

**Definition 1.6 (Static depth).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.staticDepthFor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.staticDepthFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The noncomputable depth helper selects the least exact static cardinality when one exists and returns zero otherwise.

**Definition 1.7 (Residue signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed signature exposes each residue sensor as a Boolean CUT readout on ResidueState.

**Definition 1.8 (Adaptive residue arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena packages the residue readouts, their exact fibers, an injective two-step protocol, the lower bounds, and the adaptive-versus-static depth comparison.

**Definition 1.9 (Spectrum signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed signature exposes the spectrum atom index as one five-valued CUT readout.

**Definition 1.10 (Spectrum atom arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena packages SpectrumAtom with the signature and requires the sole readout to be bijective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.AgendaReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.adaptiveDepthFor`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaFintype`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.agendaPowerSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.residueSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.spectrumSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.staticDepthFor`
- Dependency: [D5/S3/ConceptDynamics/Aggregation/AgendaPower](../Aggregation/AgendaPower.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification](../Coding/AdaptiveResidueIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope](../EscapeSpectrum/SpectrumCommitmentScope.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
