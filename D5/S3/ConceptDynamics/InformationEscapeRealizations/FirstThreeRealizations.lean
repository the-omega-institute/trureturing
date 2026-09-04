/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete readouts bind three frozen finite theorems to their realization laws. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Repository and pinned-Mathlib searches recorded in `FirstThreeArenas` found
     no legacy realization proofs for these frozen theorems.
   * Exact source hits `agenda_power`, `two_step_adaptive_residue_identification`,
     and `spectrum_atom_index_bijective` supply only the forward proofs; each
     backward implication below reconstructs the source statement from its Law.
   * The A2 `admit_readout_eq_true_iff` and `toPrimitiveBundle_agrees_iff`
     interfaces are reused for Boolean admission and kernel witnesses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas

namespace AgendaRealization
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.AgendaSource

private instance validAgendaDecidable : DecidablePred ValidAgenda := fun agenda => by
  unfold ValidAgenda
  infer_instance

def agendaPowerRealization : PrimitiveRealization agendaPowerSignature where
  readout
    | .winner => sequentialWinner majorityPrefers
    | .valid => fun agenda => decide (ValidAgenda agenda)
  anchor := fun index => Fin.elim0 index

theorem agenda_power_realization :
    LegacyPrimitiveRealization agendaPowerArena
      ((forall desired : Fin 3, exists agenda : Agenda,
        ValidAgenda agenda ∧ sequentialWinner majorityPrefers agenda = desired) ∧
      exists agenda agenda' : Agenda,
        ValidAgenda agenda ∧ ValidAgenda agenda' ∧ agenda ≠ agenda' ∧
          sequentialWinner majorityPrefers agenda ≠
            sequentialWinner majorityPrefers agenda')
      agendaPowerRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨allWinners, ⟨agenda, agenda', valid, valid', distinct, winners⟩⟩
    dsimp [agendaPowerArena, agendaPowerRealization]
    constructor
    · intro desired
      rcases allWinners desired with ⟨witness, admitted, winner⟩
      exact ⟨witness, (admit_readout_eq_true_iff ValidAgenda witness).2 admitted, winner⟩
    · exact ⟨agenda, agenda', (admit_readout_eq_true_iff ValidAgenda agenda).2 valid,
        (admit_readout_eq_true_iff ValidAgenda agenda').2 valid', distinct, winners⟩
  · intro hLaw
    dsimp [agendaPowerArena, agendaPowerRealization] at hLaw
    rcases hLaw with ⟨allWinners, ⟨agenda, agenda', valid, valid', distinct, winners⟩⟩
    constructor
    · intro desired
      rcases allWinners desired with ⟨witness, admitted, winner⟩
      exact ⟨witness, (admit_readout_eq_true_iff ValidAgenda witness).1 admitted, winner⟩
    · exact ⟨agenda, agenda', (admit_readout_eq_true_iff ValidAgenda agenda).1 valid,
        (admit_readout_eq_true_iff ValidAgenda agenda').1 valid', distinct, winners⟩

example :
    letI : Fintype Agenda := agendaFintype
    ((Finset.univ : Finset Agenda).image fun agenda =>
      (decide (ValidAgenda agenda),
        sequentialWinner majorityPrefers agenda)).card = 6 := by
  decide

example : letI : DecidableEq Agenda := inferInstance
    ¬agendaPowerRealization.toPrimitiveBundle.agrees
    (⟨1, 2, 0⟩ : Agenda) (⟨0, 0, 0⟩ : Agenda) := by
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  intro agreement
  have validAgreement := agreement.1 AgendaReadout.valid
  have leftAdmitted : ValidAgenda (⟨1, 2, 0⟩ : Agenda) := by decide
  have rightRejected : ¬ValidAgenda (⟨0, 0, 0⟩ : Agenda) := by decide
  have rightTrue : agendaPowerRealization.readout AgendaReadout.valid
      (⟨0, 0, 0⟩ : Agenda) = true := by
    rw [← validAgreement]
    exact (admit_readout_eq_true_iff ValidAgenda _).2 leftAdmitted
  exact rightRejected ((admit_readout_eq_true_iff ValidAgenda _).1 rightTrue)

example : agendaPowerArena.toArena.Nondegenerate := by decide

end AgendaRealization

namespace ResidueRealization
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.ResidueSource

def residueRealization : PrimitiveRealization residueSignature where
  readout := residueReadout
  anchor := fun index => Fin.elim0 index

private theorem adaptiveDepthFor_eq_source
    (existsExact : exists depth, ExactAtDepth residueReadout depth) :
    adaptiveDepthFor residueReadout = residueAdaptiveDepth := by
  classical
  rw [adaptiveDepthFor, dif_pos existsExact]
  unfold residueAdaptiveDepth
  congr

private theorem staticDepthFor_eq_source
    (existsExact : exists cardinality,
      StaticExactAtCardinality residueReadout cardinality) :
    staticDepthFor residueReadout = residueStaticDepth := by
  classical
  rw [staticDepthFor, dif_pos existsExact]
  unfold residueStaticDepth
  congr

private theorem staticExactExists :
    exists cardinality, StaticExactAtCardinality residueReadout cardinality := by
  refine ⟨3, Finset.univ, by decide, ?_⟩
  decide

theorem two_step_adaptive_residue_identification_realization :
    LegacyPrimitiveRealization residueArena
      ((forall state, residueReadout .two state = false <->
        state = zeroState ∨ state = tenState) ∧
      (forall state, residueReadout .two state = true <->
        state = fifteenState ∨ state = twentyOneState) ∧
      (exists protocol : BinaryProtocol ResidueState 2,
        (forall history : Fin 0 -> Bool,
          protocol.question ⟨0, by decide⟩ history = residueReadout .two) ∧
        (forall history : Fin 1 -> Bool,
          protocol.question ⟨1, by decide⟩ history =
            if history 0 then residueReadout .five else residueReadout .three) ∧
        UsesReadoutFamily residueReadout protocol ∧
        Function.Injective protocol.transcript) ∧
      (forall sensor, ¬Function.Injective (residueReadout sensor)) ∧
      (forall depth, depth < 2 -> ¬ExactAtDepth residueReadout depth) ∧
      residueAdaptiveDepth = 2 ∧ residueStaticDepth = 3 ∧
      residueAdaptiveDepth < residueStaticDepth)
      residueRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨hFalse, hTrue, hProtocol, hSensor, hBelow,
      hAdaptive, hStatic, hLess⟩
    have adaptiveExists : exists depth, ExactAtDepth residueReadout depth := by
      rcases hProtocol with ⟨protocol, hZero, hOne, hUses, hInjective⟩
      exact ⟨2, protocol, hUses, hInjective⟩
    have adaptiveEq := adaptiveDepthFor_eq_source adaptiveExists
    have staticEq := staticDepthFor_eq_source staticExactExists
    dsimp [residueArena, residueRealization]
    exact ⟨hFalse, hTrue, hProtocol, hSensor, hBelow,
      adaptiveEq.trans hAdaptive, staticEq.trans hStatic,
      by simpa [adaptiveEq, staticEq] using hLess⟩
  · intro hLaw
    dsimp [residueArena, residueRealization] at hLaw
    rcases hLaw with ⟨hFalse, hTrue, hProtocol, hSensor, hBelow,
      hAdaptive, hStatic, hLess⟩
    have adaptiveExists : exists depth, ExactAtDepth residueReadout depth := by
      rcases hProtocol with ⟨protocol, hZero, hOne, hUses, hInjective⟩
      exact ⟨2, protocol, hUses, hInjective⟩
    have adaptiveEq := adaptiveDepthFor_eq_source adaptiveExists
    have staticEq := staticDepthFor_eq_source staticExactExists
    exact ⟨hFalse, hTrue, hProtocol, hSensor, hBelow,
      adaptiveEq.symm.trans hAdaptive, staticEq.symm.trans hStatic,
      by simpa [adaptiveEq, staticEq] using hLess⟩

example :
    ((Finset.univ : Finset ResidueState).image fun state =>
      (residueReadout .two state, residueReadout .three state,
        residueReadout .five state)).card = 4 := by decide

example : ¬residueRealization.toPrimitiveBundle.agrees zeroState tenState := by
  decide

example : residueArena.toArena.Nondegenerate := by decide

end ResidueRealization

namespace SpectrumRealization
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.SpectrumSource

def spectrumRealization : PrimitiveRealization spectrumSignature where
  readout := fun _ => SpectrumAtom.index
  anchor := fun index => Fin.elim0 index

theorem spectrum_atom_index_bijective_realization :
    LegacyPrimitiveRealization spectrumArena
      (Function.Bijective SpectrumAtom.index) spectrumRealization := by
  refine ⟨?_⟩
  constructor
  · intro h
    change Function.Bijective SpectrumAtom.index
    exact h
  · intro h
    change Function.Bijective SpectrumAtom.index at h
    exact h

example :
    ((Finset.univ : Finset SpectrumAtom).image SpectrumAtom.index).card = 5 := by
  decide

example : ¬spectrumRealization.toPrimitiveBundle.agrees SpectrumAtom.t1 SpectrumAtom.t2 := by
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  intro agreement
  have indexAgreement := agreement.1 ()
  exact Fin.zero_ne_one indexAgreement

example : spectrumArena.toArena.Nondegenerate := by decide

end SpectrumRealization

end D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
