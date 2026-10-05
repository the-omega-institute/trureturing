import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyCausalMapping
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow



namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention

theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena (@Exists.{1} D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM fun (M : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) => @Exists.{1} D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM fun (N : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) => And (@Eq.{1} (Bool → Prod.{0, 0} Bool Bool) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Obs M) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Obs N)) (@Ne.{1} (Bool → Bool → Prod.{0, 0} Bool Bool) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int M) (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int N))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization := D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) (type_of% (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
    (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiObsCode M) (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiIntCode M))) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena") "__primitive_realization"),
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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention).Statement =
    (D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observation_strictly_weaker_than_intervention_realization.toTheoremUnit
      observation_strictly_weaker_than_intervention).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
