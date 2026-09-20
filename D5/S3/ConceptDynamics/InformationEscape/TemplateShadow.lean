/- GID: D5/S3/ConceptDynamics/InformationEscape/TemplateShadow
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/TemplateShadow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrum_kernel_equal; instance=D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization
   digest: Shadow registration regression checks preserve canonical arenas, primitive kernels and statements, with sensitivity witnesses and sealed query evidence. -/

/- Pure shadow realizations and kernel comparisons remain at this mathematical
owner. Reg.Catalogs.TemplateShadow imports the precise registration variants
and owns their seal and census checks. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations



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


#print axioms spectrum_bridge
#print axioms spectrum_lawSensitive

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

example : ∀ x y, interventionRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.interventionRealization.toPrimitiveBundle.agrees x y := by decide

#print axioms intervention_bridge
#print axioms intervention_lawSensitive

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

example : ∀ x y, observationRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization.toPrimitiveBundle.agrees x y := by decide

#print axioms observation_bridge
#print axioms observation_lawSensitive

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


example : ∀ x y, agendaRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.agendaPowerRealization.toPrimitiveBundle.agrees x y := by decide
#print axioms agenda_bridge
#print axioms agenda_lawSensitive

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


example : ∀ x y, preemptionRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization.toPrimitiveBundle.agrees x y := by decide
#print axioms preemption_bridge
#print axioms preemption_lawSensitive

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


example : ∀ x y, contextRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.contextRealization.toPrimitiveBundle.agrees x y := by decide
#print axioms context_bridge
#print axioms context_lawSensitive

end Context

section Static
open D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open InformationEscapeArenas.StaticExactExperimentDesign
def staticRealization := exactDesignRealization (fun x : Fin 3 => decide (x = 1)) (fun x => decide (x = 2))
theorem static_bridge : LegacyPrimitiveRealization staticExactExperimentArena
    StaticExactDesignStatement staticRealization :=
  exactDesignLegacy staticExactExperimentArena.toArena _ _
example : (exactDesignArena staticExactExperimentArena.toArena).toArena = staticExactExperimentArena.toArena := rfl
example : ∀ x y, staticRealization.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.StaticExactExperimentDesign.staticExactExperimentRealization.toPrimitiveBundle.agrees x y := by decide
theorem static_nondegenerate : staticExactExperimentArena.toArena.Nondegenerate := by decide
def staticEnumeration : Arena.StateEnumeration staticExactExperimentArena.toArena :=
  staticExactExperimentArena.__state_enumeration
theorem static_lawSensitive : staticExactExperimentArena.Law staticRealization ∧
    ¬ staticExactExperimentArena.Law (exactDesignRealization (fun _ => false) (fun _ => false)) := by
  refine ⟨static_bridge.equivalence.mp static_exact_design, ?_⟩
  intro h
  apply (by decide : (0 : Fin 3) ≠ 1)
  apply h.2.1
  funext e
  cases e <;> rfl
example : ¬ staticRealization.toPrimitiveBundle.agrees (0 : Fin 3) 1 := by decide


#print axioms static_bridge
#print axioms static_lawSensitive

end Static

section Completion
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open InformationEscapeArenas.CommutingCompletionExchange
def completionTemplate := completionExchangeRealization counterexampleF counterexampleG counterexampleReadout
def completionRealization : PrimitiveRealization completionSignature where
  readout | .flowF => completionTemplate.readout (some false)
          | .flowG => completionTemplate.readout (some true) | .cut => completionTemplate.readout none
  anchor := Fin.elim0
theorem completion_bridge : LegacyPrimitiveRealization commutingCompletionArena
    CommutativityNecessaryStatement completionRealization :=
  ⟨(completionExchangeLegacy commutingCompletionArena.toArena counterexampleF counterexampleG counterexampleReadout).equivalence⟩
example : (completionExchangeArena commutingCompletionArena.toArena Bool).toArena = commutingCompletionArena.toArena := rfl
example : ∀ x y, completionTemplate.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization.toPrimitiveBundle.agrees x y := by decide
theorem completion_nondegenerate : commutingCompletionArena.toArena.Nondegenerate := by decide
def completionEnumeration : Arena.StateEnumeration commutingCompletionArena.toArena :=
  commutingCompletionArena.__state_enumeration
theorem completion_lawSensitive : commutingCompletionArena.Law completionRealization ∧
    ¬ commutingCompletionArena.Law ⟨(fun i _ => completionRealization.readout i .d), Fin.elim0⟩ := by
  refine ⟨completion_bridge.equivalence.mp commutativity_hypothesis_is_necessary, ?_⟩
  intro h
  exact h.1 (fun _ => rfl)
example : ¬ completionTemplate.toPrimitiveBundle.agrees FourState.a FourState.b := by decide


example : ∀ x y, completionRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization.toPrimitiveBundle.agrees x y := by decide
#print axioms completion_bridge
#print axioms completion_lawSensitive

end Completion

section Gluing
open D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open InformationEscapeArenas.LocalLawGluingObstruction
def gluingTemplate := scopeTableRealization
  (fun s : Bool × Bool × Bool => s.1 = s.2.1) (fun s => s.2.1 = s.2.2) (fun s => s.1 ≠ s.2.2)
def gluingRealization : PrimitiveRealization localLawGluingSignature where
  readout | .admit01 => gluingTemplate.readout 0 | .admit12 => gluingTemplate.readout 1
          | .admit02 => gluingTemplate.readout 2
  anchor := Fin.elim0
theorem gluing_bridge : LegacyPrimitiveRealization localLawGluingArena
    LocalLawGluingStatement gluingRealization := by
  refine ⟨Iff.trans ?_ (scopeTableLegacy localLawGluingArena.toArena
    (fun s => s.1) (fun s => s.2.1) (fun s => s.2.2)
    (fun s => s.1 = s.2.1) (fun s => s.2.1 = s.2.2) (fun s => s.1 ≠ s.2.2)).equivalence⟩
  simp only [LocalLawGluingStatement, sameLaw, differentLaw, Set.ext_iff, Set.mem_image, Set.mem_ofPred_eq]
  dsimp [localLawGluingArena, Arena.ofFintype]
  simp [Bool.exists_bool, Prod.exists]
example : (scopeTableArena localLawGluingArena.toArena
    (fun s => s.1) (fun s => s.2.1) (fun s => s.2.2)).toArena = localLawGluingArena.toArena := rfl
example : ∀ x y, gluingTemplate.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.LocalLawGluingObstruction.localLawGluingRealization.toPrimitiveBundle.agrees x y := by decide
theorem gluing_nondegenerate : localLawGluingArena.toArena.Nondegenerate := by decide
def gluingEnumeration : Arena.StateEnumeration localLawGluingArena.toArena := localLawGluingArena.__state_enumeration
theorem gluing_lawSensitive : localLawGluingArena.Law gluingRealization ∧
    ¬ localLawGluingArena.Law ⟨(fun _ _ => true), Fin.elim0⟩ := by
  refine ⟨gluing_bridge.equivalence.mp compatible_local_laws_can_lack_global_state, ?_⟩
  intro h
  exact h.2.2.2 ⟨(false, false, false), rfl, rfl, rfl⟩
example : ¬ gluingTemplate.toPrimitiveBundle.agrees (false, false, false) (false, false, true) := by decide


example : ∀ x y, gluingRealization.toPrimitiveBundle.agrees x y ↔
    D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction.localLawGluingRealization.toPrimitiveBundle.agrees x y := by decide
#print axioms gluing_bridge
#print axioms gluing_lawSensitive

end Gluing

section Residue
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open FirstThreeArenas
def residueRealization := binaryFamilyRealization residueReadout
theorem residue_bridge : LegacyPrimitiveRealization residueArena
    (twoStepStatement .two .three .five zeroState tenState fifteenState twentyOneState
      residueReadout residueAdaptiveDepth residueStaticDepth) residueRealization := by
  apply twoStepLegacy residueArena.toArena .two .three .five
    zeroState tenState fifteenState twentyOneState residueReadout
example : (twoStepArena residueArena.toArena ResidueSensor .two .three .five
    zeroState tenState fifteenState twentyOneState).toArena = residueArena.toArena := rfl
example : twoStepArena residueArena.toArena ResidueSensor .two .three .five
    zeroState tenState fifteenState twentyOneState = residueArena := rfl
theorem residue_kernel_equal : ∀ x y, residueRealization.toPrimitiveBundle.agrees x y ↔
    FirstThreeRealizations.residueRealization.toPrimitiveBundle.agrees x y := by decide
theorem residue_nondegenerate : residueArena.toArena.Nondegenerate := by decide
def residueEnumeration : Arena.StateEnumeration residueArena.toArena := residueArena.__state_enumeration
theorem residue_lawSensitive : residueArena.Law residueRealization ∧
    ¬ residueArena.Law (binaryFamilyRealization (fun _ _ => false)) := by
  refine ⟨residue_bridge.equivalence.mp two_step_adaptive_residue_identification, ?_⟩
  intro h
  exact (by decide : ¬ (fifteenState = zeroState ∨ fifteenState = tenState)) (h.1 fifteenState |>.mp rfl)
example : ¬ residueRealization.toPrimitiveBundle.agrees zeroState tenState := by decide


#print axioms residue_bridge
#print axioms residue_kernel_equal
#print axioms residue_nondegenerate
#print axioms residueEnumeration
#print axioms residue_lawSensitive

end Residue

















end D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
