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



namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) (type_of% (slotRealization (fun i x => icRead i x))) (type_of% (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration/Reg.Support.LegacyCausalCoordinates.objectArena/«causal-unified-transitions»") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration/Reg.Support.LegacyCausalCoordinates.objectArena/«causal-unified-transitions»") "__primitive_realization"),
  realizationSource := some `Reg.Support.LegacyCausalFinite.ic_bridge,
  generated := false,
  arena := .object ⟨(_root_.Reg.Support.LegacyCausalSlots.icDomainArena)⟩,
  objectArena := .finite ⟨(Reg.Support.LegacyCausalCoordinates.objectArena)⟩,
  catalog := (Lean.Name.str Lean.Name.anonymous "causal-unified-transitions"),
  localNames := false,
  realization := .legacy (Reg.Support.LegacyCausalSlots.icArena) (Reg.Support.LegacyCausalFinite.icActual) (icActual.toPrimitiveBundle) ⟨(ic_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (ic_bridge) (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((icActual.toPrimitiveBundle)).Nonempty; decide),
  readout := some (slotRealization (fun i x => icRead i x)),
  variation := .evidence ⟨(ic_variation)⟩ (by first | exact (ic_variation) | exact ⟨_, _, (ic_variation)⟩),
  sensitivity := .evidence ⟨(_root_.Reg.Support.LegacyCausalSlots.ic_sensitivity)⟩ (by exact (_root_.Reg.Support.LegacyCausalSlots.ic_sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
