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



namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) (type_of% (slotRealization (fun i x => localRead i x))) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow/Reg.Support.LegacyCausalCoordinates.icObjectArena/Reg.Support.LegacyCausalCoordinates.icObjectArena") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow/Reg.Support.LegacyCausalCoordinates.icObjectArena/Reg.Support.LegacyCausalCoordinates.icObjectArena") "__primitive_realization"),
  realizationSource := some `Reg.Support.LegacyCausalFinite.local_bridge,
  generated := false,
  arena := .object ⟨(_root_.Reg.Support.LegacyCausalSlots.localDomainArena)⟩,
  objectArena := .finite ⟨(Reg.Support.LegacyCausalCoordinates.icObjectArena)⟩,
  catalog := `Reg.Support.LegacyCausalCoordinates.icObjectArena,
  localNames := false,
  realization := .legacy (Reg.Support.LegacyCausalSlots.localArena) (Reg.Support.LegacyCausalFinite.localActual) (localActual.toPrimitiveBundle) ⟨(local_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (local_bridge) (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((localActual.toPrimitiveBundle)).Nonempty; decide),
  readout := some (slotRealization (fun i x => localRead i x)),
  variation := .evidence ⟨(local_variation)⟩ (by first | exact (local_variation) | exact ⟨_, _, (local_variation)⟩),
  sensitivity := .evidence ⟨(_root_.Reg.Support.LegacyCausalSlots.local_sensitivity)⟩ (by exact (_root_.Reg.Support.LegacyCausalSlots.local_sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
