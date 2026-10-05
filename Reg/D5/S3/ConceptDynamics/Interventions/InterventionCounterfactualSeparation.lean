import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.CausalSourceFamily
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration


namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open Reg.Support.CausalSourceFamily
open LeanInformationAudit

/-- An additional source-family occurrence preserves the complete original statement. -/
noncomputable def registration : Registration separationArena (Separation actual) where
  actual := actual
  bridge := Iff.rfl
  variation := separation_variation
  sensitivity := separation_sensitivity
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) (type_of% (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "InterventionCounterfactualSeparation") "intervention_strictly_weaker_than_counterfactual") "Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation/Reg.Support.CausalSourceFamily.separationArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(separationArena)⟩,
  objectArena := .source ⟨(separationArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (separationArena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["arg", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily
