import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.GeneratorRowInstability
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.GeneratorRowInstability
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.GeneratorRowInstability

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℂ
  State _ := ZMod 9
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => targetSpectrum p.1 p.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (A : ℝ), 1 ≤ A → ∀ (u : ℂ), ‖u‖ = 1 →
    FamilyProperties A u (R.readout () ⟨A, u⟩)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h 1 (by norm_num) 1 (by norm_num)
  have hm := hp.magnitude 1
  norm_num (config := { decide := true }) [Fin.ext_iff, rejected, realize, sourceSpectrum] at hm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  norm_num (config := { decide := true })
    [Fin.ext_iff, actual, realize, targetSpectrum, sourceSpectrum, blockPhase]

def registration : Registration arena (type_of% (@parameter_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parameter_family, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@parameter_family)
    (type_of% (realize signature (fun _ p k => targetSpectrum p.1 p.2 k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.GeneratorRowInstability.parameter_family.information_unit,
  realizationName := `Reg.D5.S3.Fourier.GeneratorRowInstability.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p k => targetSpectrum p.1 p.2 k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.GeneratorRowInstability,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.Fourier.GeneratorRowInstability
end
