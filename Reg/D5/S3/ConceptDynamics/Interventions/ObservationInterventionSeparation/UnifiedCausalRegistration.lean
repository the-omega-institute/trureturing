import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyCausalFinite
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses



namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) (type_of% (_root_.Reg.Support.LegacyCausalSlots.oiDomainArena)) (type_of% (Reg.Support.LegacyCausalCoordinates.objectArena)) (type_of% (slotRealization (fun i x => oiRead i x))) (type_of% (oi_variation)) (type_of% (_root_.Reg.Support.LegacyCausalSlots.oi_sensitivity)) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration/Reg.Support.LegacyCausalCoordinates.objectArena/«causal-unified-transitions»") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "ObservationInterventionSeparation") "observation_strictly_weaker_than_intervention") "Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration/Reg.Support.LegacyCausalCoordinates.objectArena/«causal-unified-transitions»") "__primitive_realization"),
  realizationSource := some `Reg.Support.LegacyCausalFinite.oi_bridge,
  generated := false,
  arena := ⟨(_root_.Reg.Support.LegacyCausalSlots.oiDomainArena)⟩,
  objectArena := ⟨(Reg.Support.LegacyCausalCoordinates.objectArena)⟩,
  catalog := (Lean.Name.str Lean.Name.anonymous "causal-unified-transitions"),
  localNames := false,
  realization := .legacy (Reg.Support.LegacyCausalSlots.oiArena) (Reg.Support.LegacyCausalFinite.oiActual) (oiActual.toPrimitiveBundle) ⟨(oi_bridge)⟩,
  readout := some (slotRealization (fun i x => oiRead i x)),
  variation := some ⟨(oi_variation)⟩,
  sensitivity := some ⟨(_root_.Reg.Support.LegacyCausalSlots.oi_sensitivity)⟩,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
