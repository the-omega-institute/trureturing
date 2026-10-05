import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyRelations.Preemption
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit



namespace Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
attribute [local instance]
  contextDecidableEq
  modelDecidableEq
local instance systemArenaStateDecidableEq : DecidableEq arena.toArena.State :=
  arena.toArena.stateDecidableEq

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) (type_of% (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual.readout Reg.Support.LegacyRelations.Preemption.actual.anchor)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(endStateOmitsPreemptingCauseArena)⟩,
  objectArena := .law ⟨(endStateOmitsPreemptingCauseArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (endStateOmitsPreemptingCauseArena) (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization) (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature (fun (a b : D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace) => @Fintype.decidablePiFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (a_1 b : Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) => @Option.instDecidableEq.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.instDecidableEqMechanism a_1 b) (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b) D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization) ⟨(end_state_omits_preempting_cause_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (end_state_omits_preempting_cause_realization) (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature (fun (a b : D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace) => @Fintype.decidablePiFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (a_1 b : Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) => @Option.instDecidableEq.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.instDecidableEqMechanism a_1 b) (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b) D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)).Nonempty; decide),
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual.readout Reg.Support.LegacyRelations.Preemption.actual.anchor),
  variation := .evidence ⟨(Reg.Support.LegacyRelations.Preemption.finite_variation)⟩ (by first | exact (Reg.Support.LegacyRelations.Preemption.finite_variation) | exact ⟨_, _, (Reg.Support.LegacyRelations.Preemption.finite_variation)⟩),
  sensitivity := .evidence ⟨(Reg.Support.LegacyRelations.Preemption.finite_sensitivity)⟩ (by exact (Reg.Support.LegacyRelations.Preemption.finite_sensitivity)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }, { path := #["arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := some ⟨_, ⟨(Reg.Support.LegacyRelations.Preemption.registration)⟩⟩,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot
