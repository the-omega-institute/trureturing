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



namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) (type_of% (_root_.Reg.Support.LegacyCausalSlots.localDomainArena)) (type_of% (Reg.Support.LegacyCausalCoordinates.icObjectArena)) (type_of% (slotRealization (fun i x => localRead i x))) (type_of% (local_variation)) (type_of% (_root_.Reg.Support.LegacyCausalSlots.local_sensitivity)) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot/Reg.Support.LegacyCausalCoordinates.icObjectArena/Reg.Support.LegacyCausalCoordinates.icObjectArena") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot/Reg.Support.LegacyCausalCoordinates.icObjectArena/Reg.Support.LegacyCausalCoordinates.icObjectArena") "__primitive_realization"),
  realizationSource := some `Reg.Support.LegacyCausalFinite.local_bridge,
  generated := false,
  arena := ⟨(_root_.Reg.Support.LegacyCausalSlots.localDomainArena)⟩,
  objectArena := ⟨(Reg.Support.LegacyCausalCoordinates.icObjectArena)⟩,
  catalog := `Reg.Support.LegacyCausalCoordinates.icObjectArena,
  localNames := false,
  realization := .legacy (Reg.Support.LegacyCausalSlots.localArena) (Reg.Support.LegacyCausalFinite.localActual) (localActual.toPrimitiveBundle) ⟨(local_bridge)⟩,
  readout := some (slotRealization (fun i x => localRead i x)),
  variation := some ⟨(local_variation)⟩,
  sensitivity := some ⟨(_root_.Reg.Support.LegacyCausalSlots.local_sensitivity)⟩,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
