import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.CausalSourceFamily

namespace Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open Reg.Support.CausalSourceFamily
open LeanInformationAudit

/-- An additional source-family occurrence preserves the complete original statement. -/
noncomputable def registration : Registration strictnessArena (Strictness actual) where
  actual := actual
  bridge := Iff.rfl
  variation := strictness_variation
  sensitivity := strictness_sensitivity
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer) (type_of% (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualKernelStrictlyFiner") "counterfactual_kernel_strictly_finer") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily/Reg.Support.CausalSourceFamily.strictnessArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(strictnessArena)⟩,
  objectArena := .source ⟨(strictnessArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (strictnessArena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "domain", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.SourceFamily
