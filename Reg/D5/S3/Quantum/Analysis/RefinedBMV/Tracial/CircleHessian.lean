import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.CircleHessian
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.CircleHessian

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV.Tracial (fourMarkTraceInsertionDefect fourMarkTraceHessian_lower)
open LeanInformationAudit
open scoped Matrix Matrix.Norms.Frobenius

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq (1 / 2 : ℝ)
  norm_num [actual, realize] at h

abbrev arena : Arena where
  signature := signature
  Law Q := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (h b : ι → ℝ)
    (X : Matrix ι ι ℂ) (_hX : X.IsHermitian) {R : ℝ} (_hR : ∀ i, -R ≤ h i),
    let B : Matrix ι ι ℂ := Matrix.diagonal fun i ↦ (b i : ℂ)
    Q.readout () () ((Real.exp (-R) / 40) * ‖B * (X * B - B * X)‖ ^ 2)
      ((∫ s in (0 : ℝ)..1, fourMarkTraceInsertionDefect h b X s) / 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) (fun _ ↦ 0) (fun _ ↦ 0) 0
    (by simp [Matrix.IsHermitian]) (R := 0) (by simp)

def hessianFamily : Registration arena.{u} (type_of% @fourMarkTraceHessian_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fourMarkTraceHessian_lower.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    rejected rejected_law
  dependence := dependence

def hessianRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fourMarkTraceHessian_lower.{u}) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.Tracial.fourMarkTraceHessian_lower.__information_unit
  realizationName := ``hessianFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨hessianFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.CircleHessian
