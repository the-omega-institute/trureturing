# First Three Legacy Primitive Realizations

## Abstract

The first three frozen statements are equivalent to their realization laws.

**Definition 1.1 (Agenda power realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.agendaPowerRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.agendaPowerRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed realization reads the sequential majority winner and decides ValidAgenda, with no point anchors.

**Theorem 1.2 (Agenda power realization certificate).**

$$((\forall desired: \operatorname{Fin}(3), \exists agenda: Agenda, (\operatorname{ValidAgenda}(agenda)) \land (\operatorname{sequentialWinner}(majorityPrefers, agenda) = desired)) \land (\exists agenda agenda': Agenda, (\operatorname{ValidAgenda}(agenda)) \land (\operatorname{ValidAgenda}(agenda')) \land (agenda \neq agenda') \land (\operatorname{sequentialWinner}(majorityPrefers, agenda) \neq \operatorname{sequentialWinner}(majorityPrefers, agenda')))) \iff agendaPowerArena.Law agendaPowerRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.agenda_power_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate identifies the full frozen agenda-power proposition with agendaPowerArena.Law agendaPowerRealization.

**Definition 1.3 (Residue realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.residueRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.residueRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed realization uses residueReadout at every residue sensor and has no point anchors.

**Theorem 1.4 (Adaptive residue realization certificate).**

$$((\forall state: ResidueState, \operatorname{residueReadout}(ResidueSensor.two, state) = false \iff (state = zeroState) \lor (state = tenState)) \land (\forall state: ResidueState, \operatorname{residueReadout}(ResidueSensor.two, state) = true \iff (state = fifteenState) \lor (state = twentyOneState)) \land (\exists protocol: \operatorname{BinaryProtocol}(ResidueState, 2), (\forall history: \operatorname{Fin}(0) \to Bool, protocol.question(\langle0, by decide\rangle, history) = \operatorname{residueReadout}(ResidueSensor.two)) \land (\forall history: \operatorname{Fin}(1) \to Bool, protocol.question(\langle1, by decide\rangle, history) = \operatorname{if}(\operatorname{history}(0), \operatorname{residueReadout}(ResidueSensor.five), \operatorname{residueReadout}(ResidueSensor.three))) \land (\operatorname{UsesReadoutFamily}(residueReadout, protocol)) \land (Function.Injective(protocol.transcript))) \land (\forall sensor: ResidueSensor, \neg Function.Injective(\operatorname{residueReadout}(sensor))) \land (\forall depth: Nat, depth < 2 \Rightarrow \neg \operatorname{ExactAtDepth}(residueReadout, depth)) \land (residueAdaptiveDepth = 2) \land (residueStaticDepth = 3) \land (residueAdaptiveDepth < residueStaticDepth)) \iff residueArena.Law residueRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.two_step_adaptive_residue_identification_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate identifies every clause of the frozen adaptive-residue proposition with residueArena.Law residueRealization.

**Definition 1.5 (Spectrum realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.spectrumRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.spectrumRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed realization reads SpectrumAtom.index at the sole readout and has no point anchors.

**Theorem 1.6 (Spectrum index realization certificate).**

$$(Function.Bijective(SpectrumAtom.index)) \iff spectrumArena.Law spectrumRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.spectrum_atom_index_bijective_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate identifies Function.Bijective SpectrumAtom.index with spectrumArena.Law spectrumRealization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.agendaPowerRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.agenda_power_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.residueRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.spectrumRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.spectrum_atom_index_bijective_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.two_step_adaptive_residue_identification_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas](../InformationEscapeArenas/FirstThreeArenas.md)
