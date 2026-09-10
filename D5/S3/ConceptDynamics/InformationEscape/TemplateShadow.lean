/- GID: D5/S3/ConceptDynamics/InformationEscape/TemplateShadow
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/TemplateShadow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrum_kernel_equal; instance=D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization
   digest: Shadow registration regression checks preserve canonical arenas, primitive kernels and statements, with sensitivity witnesses and sealed query evidence. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

open RegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscapeArenas
open D5.S3.ConceptDynamics.InformationEscapeRealizations

section Spectrum
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open FirstThreeArenas
def spectrumRealization := cutRealization SpectrumAtom.index
theorem spectrum_bridge : LegacyPrimitiveRealization spectrumArena
    (Function.Bijective SpectrumAtom.index) spectrumRealization :=
  bijectiveLegacy spectrumArena.toArena SpectrumAtom.index
example : (bijectiveArena spectrumArena.toArena (Fin 5)).toArena = spectrumArena.toArena := rfl
theorem spectrum_kernel_equal : ∀ x y, spectrumRealization.toPrimitiveBundle.agrees x y ↔
    FirstThreeRealizations.spectrumRealization.toPrimitiveBundle.agrees x y := by decide
example : spectrumArena.Law spectrumRealization ↔ Function.Bijective SpectrumAtom.index := Iff.rfl
theorem spectrum_nondegenerate : spectrumArena.toArena.Nondegenerate := by decide
def spectrumEnumeration : Arena.StateEnumeration spectrumArena.toArena := spectrumArena.__state_enumeration
theorem spectrum_lawSensitive : spectrumArena.Law spectrumRealization ∧
    ¬ spectrumArena.Law (cutRealization (fun _ => (0 : Fin 5))) := by
  refine ⟨spectrum_bridge.equivalence.mp spectrum_atom_index_bijective, ?_⟩
  intro h
  exact (by decide : SpectrumAtom.t1 ≠ SpectrumAtom.t2) (h.1 rfl)
example : ¬ spectrumRealization.toPrimitiveBundle.agrees SpectrumAtom.t1 SpectrumAtom.t2 := by decide
register_information_theorem spectrum_atom_index_bijective in spectrumArena
  primitives spectrumRealization.toPrimitiveBundle realization spectrum_bridge
end Spectrum

section Intervention
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq
def interventionTemplate := separationRealization Int CF
def interventionRealization : PrimitiveRealization interventionSignature where
  readout | .intervention => interventionTemplate.readout false
          | .counterfactual => interventionTemplate.readout true
  anchor := Fin.elim0
theorem intervention_bridge : LegacyPrimitiveRealization interventionArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  ⟨(separationLegacy interventionArena.toArena Int CF).equivalence⟩
example : (separationArena interventionArena.toArena
    (Bool → Bool → Nat) (Bool → Bool → Bool → Bool)).toArena = interventionArena.toArena := rfl
example : ∀ x y, interventionTemplate.toPrimitiveBundle.agrees x y ↔
    FourthFifthRealizations.interventionRealization.toPrimitiveBundle.agrees x y := by decide
example : interventionArena.Law interventionRealization ↔
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) := Iff.rfl
theorem intervention_nondegenerate : interventionArena.toArena.Nondegenerate := by decide
def interventionEnumeration : Arena.StateEnumeration interventionArena.toArena :=
  interventionArena.__state_enumeration
theorem intervention_lawSensitive : interventionArena.Law interventionRealization ∧
    ¬ interventionArena.Law ⟨(fun i _ => interventionRealization.readout i noEffectModel), Fin.elim0⟩ := by
  refine ⟨intervention_bridge.equivalence.mp intervention_strictly_weaker_than_counterfactual, ?_⟩
  rintro ⟨x, y, _, h⟩
  exact h rfl
example : ¬ interventionTemplate.toPrimitiveBundle.agrees noEffectModel flipEffectModel := by decide
register_information_theorem intervention_strictly_weaker_than_counterfactual in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization intervention_bridge
end Intervention

section Observation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention
def observationTemplate := separationRealization Obs Int
def observationRealization : PrimitiveRealization observationInterventionSignature where
  readout | .observation => observationTemplate.readout false
          | .intervention => observationTemplate.readout true
  anchor := Fin.elim0
theorem observation_bridge : LegacyPrimitiveRealization observationInterventionArena
    ObservationInterventionStatement observationRealization :=
  ⟨(separationLegacy observationInterventionArena.toArena Obs Int).equivalence⟩
example : (separationArena observationInterventionArena.toArena
    (Bool → Bool × Bool) (Bool → Bool → Bool × Bool)).toArena = observationInterventionArena.toArena := rfl
example : ∀ x y, observationTemplate.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization.toPrimitiveBundle.agrees x y := by decide
example : observationInterventionArena.Law observationRealization ↔ ObservationInterventionStatement := Iff.rfl
theorem observation_nondegenerate : observationInterventionArena.toArena.Nondegenerate := by decide
def observationEnumeration : Arena.StateEnumeration observationInterventionArena.toArena :=
  observationInterventionArena.__state_enumeration
theorem observation_lawSensitive : observationInterventionArena.Law observationRealization ∧
    ¬ observationInterventionArena.Law ⟨(fun i _ => observationRealization.readout i xCausesYModel), Fin.elim0⟩ := by
  refine ⟨observation_bridge.equivalence.mp observation_strictly_weaker_than_intervention, ?_⟩
  rintro ⟨x, y, _, h⟩
  exact h rfl
example : ¬ observationTemplate.toPrimitiveBundle.agrees xCausesYModel yCausesXModel := by decide
register_information_theorem observation_strictly_weaker_than_intervention in observationInterventionArena
  primitives observationRealization.toPrimitiveBundle realization observation_bridge
end Observation

section Agenda
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
open FirstThreeArenas
attribute [local instance] agendaFintype
local instance : DecidablePred ValidAgenda := fun _ => by unfold ValidAgenda; infer_instance
def agendaTemplate := admittedSurjectionRealization (sequentialWinner majorityPrefers) ValidAgenda
def agendaRealization : PrimitiveRealization agendaPowerSignature where
  readout | .winner => agendaTemplate.readout false | .valid => agendaTemplate.readout true
  anchor := Fin.elim0
theorem agenda_bridge : LegacyPrimitiveRealization agendaPowerArena
    ((∀ desired : Fin 3, ∃ a : Agenda, ValidAgenda a ∧ sequentialWinner majorityPrefers a = desired) ∧
      ∃ a b : Agenda, ValidAgenda a ∧ ValidAgenda b ∧ a ≠ b ∧
        sequentialWinner majorityPrefers a ≠ sequentialWinner majorityPrefers b) agendaRealization :=
  ⟨(admittedSurjectionLegacy agendaPowerArena.toArena (sequentialWinner majorityPrefers) ValidAgenda).equivalence⟩
example : (admittedSurjectionArena agendaPowerArena.toArena (Fin 3)).toArena = agendaPowerArena.toArena := rfl
example : ∀ x y, agendaTemplate.toPrimitiveBundle.agrees x y ↔
    FirstThreeRealizations.agendaPowerRealization.toPrimitiveBundle.agrees x y := by decide
theorem agenda_nondegenerate : agendaPowerArena.toArena.Nondegenerate := by decide
def agendaEnumeration : Arena.StateEnumeration agendaPowerArena.toArena := agendaPowerArena.__state_enumeration
theorem agenda_lawSensitive : agendaPowerArena.Law agendaRealization ∧
    ¬ agendaPowerArena.Law ⟨(fun i _ => agendaRealization.readout i ⟨0, 0, 0⟩), Fin.elim0⟩ := by
  refine ⟨agenda_bridge.equivalence.mp agenda_power, ?_⟩
  rintro ⟨_, a, b, _, _, _, h⟩
  exact h rfl
example : ¬ agendaTemplate.toPrimitiveBundle.agrees (⟨1, 2, 0⟩ : Agenda) ⟨0, 0, 0⟩ := by decide
register_information_theorem agenda_power in agendaPowerArena
  primitives agendaRealization.toPrimitiveBundle realization agenda_bridge
example : agenda_power.__information_unit.Statement =
    (FirstThreeRealizations.agenda_power_realization.toTheoremUnit agenda_power).Statement := rfl
end Agenda

section Preemption
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open InformationEscapeArenas.EndStateOmitsPreemptingCause
def preemptionTemplate := anchoredSeparationRealization endState activeCause
  (fun t => IsOrderedPreemption t .shooterA .shooterB)
  (fun t => IsOrderedPreemption t .shooterB .shooterA) aThenB bThenA
def preemptionRealization : PrimitiveRealization preemptionSignature where
  readout | .cutEnd => preemptionTemplate.readout 0 | .cutCause => preemptionTemplate.readout 1
          | .admitAThenB => preemptionTemplate.readout 2 | .admitBThenA => preemptionTemplate.readout 3
  anchor | .aThenB => preemptionTemplate.anchor false | .bThenA => preemptionTemplate.anchor true
theorem preemption_bridge : LegacyPrimitiveRealization endStateOmitsPreemptingCauseArena
    EndStateOmitsPreemptingCauseStatement preemptionRealization :=
  ⟨(anchoredSeparationLegacy endStateOmitsPreemptingCauseArena.toArena endState activeCause
    (fun t => IsOrderedPreemption t .shooterA .shooterB)
    (fun t => IsOrderedPreemption t .shooterB .shooterA) aThenB bThenA).equivalence⟩
example : (anchoredSeparationArena endStateOmitsPreemptingCauseArena.toArena Bool
    (Option Mechanism)).toArena = endStateOmitsPreemptingCauseArena.toArena := rfl
example : ∀ x y, preemptionTemplate.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization.toPrimitiveBundle.agrees x y := by decide
theorem preemption_nondegenerate : endStateOmitsPreemptingCauseArena.toArena.Nondegenerate := by decide
def preemptionEnumeration : Arena.StateEnumeration endStateOmitsPreemptingCauseArena.toArena :=
  endStateOmitsPreemptingCauseArena.__state_enumeration
theorem preemption_lawSensitive : endStateOmitsPreemptingCauseArena.Law preemptionRealization ∧
    ¬ endStateOmitsPreemptingCauseArena.Law
      ⟨(fun i _ => preemptionRealization.readout i aThenB), fun _ => aThenB⟩ := by
  refine ⟨preemption_bridge.equivalence.mp end_state_omits_preempting_cause, ?_⟩
  intro h
  exact h.2.2.2.1 rfl
example : ¬ preemptionTemplate.toPrimitiveBundle.agrees aThenB bThenA := by decide
register_information_theorem end_state_omits_preempting_cause in endStateOmitsPreemptingCauseArena
  primitives preemptionRealization.toPrimitiveBundle realization preemption_bridge
example : end_state_omits_preempting_cause.__information_unit.Statement =
    (InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
      end_state_omits_preempting_cause).Statement := rfl
end Preemption

section Context
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open FourthFifthArenas
attribute [local instance] contextFintype contextDecidableEq
local instance (c : BinaryInterpretationContext) (b : Bool) :
    Decidable (IsBinaryFixedMeaning c (b, b, b)) := by unfold IsBinaryFixedMeaning; infer_instance
def contextTemplate := contextSelectionRealization
  (fun c : BinaryInterpretationContext => c.text) (fun c => c.interpretationRule)
  (fun c => c.readerAdmission) (fun c => c.background) (fun c => c.evaluationGoal)
  (fun c => IsBinaryFixedMeaning c (false, false, false))
  (fun c => IsBinaryFixedMeaning c (true, true, true)) baselineContext alternateContext
def contextRealization : PrimitiveRealization contextSignature where
  readout | .text => contextTemplate.readout 0 | .interpretationRule => contextTemplate.readout 1
          | .readerAdmission => contextTemplate.readout 2 | .background => contextTemplate.readout 3
          | .evaluationGoal => contextTemplate.readout 4 | .falseMeaning => contextTemplate.readout 5
          | .trueMeaning => contextTemplate.readout 6
  anchor := contextTemplate.anchor
theorem context_bridge : LegacyPrimitiveRealization contextArena
    (baselineContext.text = alternateContext.text ∧
      baselineContext.interpretationRule = alternateContext.interpretationRule ∧
      baselineContext.readerAdmission ≠ alternateContext.readerAdmission ∧
      baselineContext.background ≠ alternateContext.background ∧
      baselineContext.evaluationGoal ≠ alternateContext.evaluationGoal ∧
      IsBinaryFixedMeaning baselineContext (false, false, false) ∧
      IsBinaryFixedMeaning alternateContext (true, true, true) ∧
      (false, false, false) ≠ (true, true, true)) contextRealization :=
  ⟨(contextSelectionLegacy contextArena.toArena
    (fun c => c.text) (fun c => c.interpretationRule)
    (fun c => c.readerAdmission) (fun c => c.background) (fun c => c.evaluationGoal)
    (fun c => IsBinaryFixedMeaning c (false, false, false))
    (fun c => IsBinaryFixedMeaning c (true, true, true)) baselineContext alternateContext).equivalence⟩
example : (contextSelectionArena contextArena.toArena Unit Unit).toArena = contextArena.toArena := rfl
example : ∀ x y, contextTemplate.toPrimitiveBundle.agrees x y ↔
    FourthFifthRealizations.contextRealization.toPrimitiveBundle.agrees x y := by decide
theorem context_nondegenerate : contextArena.toArena.Nondegenerate := by decide
def contextEnumeration : Arena.StateEnumeration contextArena.toArena := contextArena.__state_enumeration
theorem context_lawSensitive : contextArena.Law contextRealization ∧
    ¬ contextArena.Law ⟨(fun i _ => contextRealization.readout i baselineContext), fun _ => baselineContext⟩ := by
  refine ⟨context_bridge.equivalence.mp context_parameters_can_select_distinct_fixed_points, ?_⟩
  intro h
  exact h.2.2.1 rfl
example : ¬ contextTemplate.toPrimitiveBundle.agrees baselineContext alternateContext := by decide
register_information_theorem context_parameters_can_select_distinct_fixed_points in contextArena
  primitives contextRealization.toPrimitiveBundle realization context_bridge
example : context_parameters_can_select_distinct_fixed_points.__information_unit.Statement =
    (FourthFifthRealizations.context_parameters_can_select_distinct_fixed_points_realization.toTheoremUnit
      context_parameters_can_select_distinct_fixed_points).Statement := rfl
end Context

end D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
