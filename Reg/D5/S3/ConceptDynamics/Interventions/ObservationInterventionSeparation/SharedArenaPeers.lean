import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers



namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention

theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena (@Exists.{1} D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM fun (M : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) => @Exists.{1} D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM fun (N : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) => And (@Eq.{1} (Bool → Prod.{0, 0} Bool Bool) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Obs M) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Obs N)) (@Ne.{1} (Bool → Bool → Prod.{0, 0} Bool Bool) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int M) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int N))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization := D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) (type_of% (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))) (type_of% (DeterministicBoolSCM)) (type_of% (finiteObservationResidual)) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge,
  generated := false,
  arena := .law ⟨(finiteObservationInterventionLawArena)⟩,
  objectArena := .finite ⟨(finiteObservationInterventionArena)⟩,
  catalog := `finiteProbe,
  localNames := false,
  realization := .legacy (finiteObservationInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization) (finiteObservationRealization.toPrimitiveBundle) ⟨(finiteObservation_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (finiteObservation_bridge) (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((finiteObservationRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M)),
  variation := .evidence ⟨(finiteObservation_law_sensitive)⟩ (by first | exact (finiteObservation_law_sensitive) | exact ⟨_, _, (finiteObservation_law_sensitive)⟩),
  sensitivity := .evidence ⟨(finiteObservation_slot_sensitive)⟩ (by exact (finiteObservation_slot_sensitive)),
  partialSensitivity := none,
  escapeFrom := some (DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .evidence ⟨(finiteObservationResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation, declaration := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers


noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"SharedArenaPeers\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"SharedArenaPeers\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.Arena.{0} :=
  D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"SharedArenaPeers\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Interventions\",\"ObservationInterventionSeparation\",\"SharedArenaPeers\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers, declaration := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
