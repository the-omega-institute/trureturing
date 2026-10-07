import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact1, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact2, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact3, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.descriptorFact, `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.liftedActualFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.statementExclusion,
  finiteLift := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.finiteLiftFacts,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.anchorEnumeration }

end

end Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot


noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.Support.LegacyRelations.Preemption.arena) (Reg.Support.LegacyRelations.Preemption.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.Support.LegacyRelations.Preemption.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout) where
  values := [D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd, D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause, D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB, D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor) where
  values := [D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB, D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation0 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature
    D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd PUnit.unit.{1}

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [.argument, .argument, .function, .argument, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation1 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature
    D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause PUnit.unit.{1}

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [.argument, .argument, .argument, .function, .argument, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation2 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB
  PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB
  PUnit.unit.{1} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.aThenB

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact2 : LeanInformationAudit.Contract.BoolReflection
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[\"function\",\"argument\"],\"levels\":[]}"))
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"observation2\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) :=
  { sourceAt := { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [.function, .argument], levels := [] }, readoutAt := { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation2, part := .value, path := [], levels := [] }, reflects := by change (_ ↔ decide (_ : Prop) = true); simp only [decide_eq_true_eq] }

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation3 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA
  PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA
  PUnit.unit.{1} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.bThenA

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observationFact3 : LeanInformationAudit.Contract.BoolReflection
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[\"argument\",\"function\",\"argument\"],\"levels\":[]}"))
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"observation3\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) :=
  { sourceAt := { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [.argument, .function, .argument], levels := [] }, readoutAt := { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.observation3, part := .value, path := [], levels := [] }, reflects := by change (_ ↔ decide (_ : Prop) = true); simp only [decide_eq_true_eq] }

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.varyingLaw : (r :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
      Reg.Support.LegacyRelations.Preemption.signature) →
  Prop :=
  fun
    (r :
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
        Reg.Support.LegacyRelations.Preemption.signature) =>
  And
    (@Eq.{1}
      (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.Support.LegacyRelations.Preemption.signature
        D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB
        Unit.unit)
      (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
        Reg.Support.LegacyRelations.Preemption.signature r
        D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB
        Unit.unit
        (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Preemption.signature r
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB Unit.unit))
      Bool.true)
    (And
      (@Eq.{1}
        (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Preemption.signature
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA
          Unit.unit)
        (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Preemption.signature r
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA
          Unit.unit
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Preemption.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA
            Unit.unit))
        Bool.true)
      (And
        (@Eq.{1}
          (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Preemption.signature
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd
            Unit.unit)
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Preemption.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd
            Unit.unit
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Preemption.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB
              Unit.unit))
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Preemption.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd
            Unit.unit
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Preemption.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA
              Unit.unit)))
        (And
          (@Ne.{1}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Preemption.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Preemption.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause
              Unit.unit
              (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
                Reg.Support.LegacyRelations.Preemption.signature r
                D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB
                Unit.unit))
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Preemption.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause
              Unit.unit
              (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor.{0, 0, 0, 0, 0}
                Reg.Support.LegacyRelations.Preemption.signature r
                D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA
                Unit.unit)))
          (Not
            (@Exists.{1} (Bool → Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism)
              fun
                (recover :
                  Bool → Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) =>
              @Eq.{1}
                (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                    Reg.Support.LegacyRelations.Preemption.signature Unit.unit →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.Support.LegacyRelations.Preemption.signature
                    D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause
                    Unit.unit)
                (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
                  Reg.Support.LegacyRelations.Preemption.signature r
                  D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause
                  Unit.unit)
                (@Function.comp.{1, 1, 1}
                  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                    Reg.Support.LegacyRelations.Preemption.signature Unit.unit)
                  Bool (Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) recover
                  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
                    Reg.Support.LegacyRelations.Preemption.signature r
                    D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd
                    Unit.unit)))))))

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"end_state_omits_preempting_cause\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.Support.LegacyRelations.Preemption.registration).actual (Reg.Support.LegacyRelations.Preemption.registration).variation.2.choose (Reg.Support.LegacyRelations.Preemption.registration).variation.1 (Reg.Support.LegacyRelations.Preemption.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"Preemption\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.Support.LegacyRelations.Preemption, declaration := `Reg.Support.LegacyRelations.Preemption.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.finiteLiftFacts : LeanInformationAudit.Contract.FiniteLiftFacts (D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena) (Reg.Support.LegacyRelations.Preemption.arena) (@Reg.Support.LegacyRelations.Preemption.fromLegacy) (@Reg.Support.LegacyRelations.Preemption.toLegacy) where
  lowerLift := Reg.Support.LegacyRelations.Preemption.to_from_legacy
  liftLower := Reg.Support.LegacyRelations.Preemption.from_to_legacy
  law := by intro r; rw [Reg.Support.LegacyRelations.Preemption.full_law_transport, Reg.Support.LegacyRelations.Preemption.to_from_legacy]
  observations := []

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.liftedActual : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Preemption.signature :=
  Reg.Support.LegacyRelations.Preemption.fromLegacy
  D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization

noncomputable def Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.liftedActualFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"Preemption\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Attribution\",\"EndStateOmitsPreemptingCause\",\"InformationRoot\",\"registration_1\",\"liftedActual\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.Support.LegacyRelations.Preemption, declaration := `Reg.Support.LegacyRelations.Preemption.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot.registration_1.liftedActual, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))
