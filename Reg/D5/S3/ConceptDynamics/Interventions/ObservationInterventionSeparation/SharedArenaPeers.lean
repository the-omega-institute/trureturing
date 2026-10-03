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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) (type_of% (finiteObservationInterventionLawArena)) (type_of% (finiteObservationInterventionArena)) (type_of% (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))) (type_of% (finiteObservation_law_sensitive)) (type_of% (finiteObservation_slot_sensitive)) (type_of% (DeterministicBoolSCM)) (type_of% (finiteObservationResidual)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge,
  generated := false,
  arena := ⟨(finiteObservationInterventionLawArena)⟩,
  objectArena := ⟨(finiteObservationInterventionArena)⟩,
  catalog := `finiteProbe,
  localNames := false,
  realization := .legacy (finiteObservationInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization) (finiteObservationRealization.toPrimitiveBundle) ⟨(finiteObservation_bridge)⟩,
  readout := some (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M)),
  variation := some ⟨(finiteObservation_law_sensitive)⟩,
  sensitivity := some ⟨(finiteObservation_slot_sensitive)⟩,
  escapeFrom := some (DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .evidence ⟨(finiteObservationResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers
