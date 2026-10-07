import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyCausalMapping
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



namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) (type_of% (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
    (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiObsCode M) (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiIntCode M))) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge,
  generated := false,
  arena := .law ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena)⟩,
  objectArena := .finite ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)⟩,
  catalog := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena,
  localNames := false,
  realization := .legacy (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization) (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization.toPrimitiveBundle) ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge) (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
    (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiObsCode M) (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiIntCode M)),
  variation := .evidence ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_law_sensitive)⟩ (by first | exact (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_law_sensitive) | exact ⟨_, _, (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_law_sensitive)⟩),
  sensitivity := .evidence ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_slot_sensitive)⟩ (by exact (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_slot_sensitive)),
  partialSensitivity := none,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation, declaration := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot


noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"InformationRoot\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"InformationRoot\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.Arena.{0} :=
  D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"InformationRoot\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"InformationRoot\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
