import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.ExpandingAverage
import Reg.Support.SingleDependentReadout

/-! Full-source registration for the expanding inverse-adjoint average. -/

namespace Reg.D5.S3.Quantum.Schatten.ExpandingAverage
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Matrix (Fin n) (Fin n) ℂ)
    (fun _ => ℝ) (fun p => Matrix (Fin p.1) (Fin p.1) ℂ)

def actual : Realization signature :=
  realize signature (fun _ p t =>
    (inverseAdjointAverage p.2 t)ᴴ * inverseAdjointAverage p.2 t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ), IsUnit W.det →
    ∀ (t : ℝ), 0 < t → (R.readout () ⟨n, W⟩ t - 1).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 (by simp) 1 (by norm_num)
  dsimp only [signature, Reg.Support.SingleDependentReadout.signature, rejected, realize] at hh
  simp only [zero_sub] at hh
  change Matrix.PosSemidef (-(1 : Matrix (Fin 1) (Fin 1) ℂ)) at hh
  have hd := hh.diag_nonneg (i := (0 : Fin 1))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (1 : Matrix (Fin 1) (Fin 1) ℂ)⟩, (1 : ℝ), (2 : ℝ), ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
  norm_num [actual, realize, inverseAdjointAverage, Matrix.mul_apply,
    Matrix.smul_apply, Complex.ext_iff] at he

def source_registration : Registration arena (type_of% @inverseAdjointAverage_expanding) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverseAdjointAverage_expanding, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverseAdjointAverage_expanding) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Schatten.ExpandingAverage.unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ExpandingAverage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t =>
    (inverseAdjointAverage p.2 t)ᴴ * inverseAdjointAverage p.2 t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ExpandingAverage
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Schatten.ExpandingAverage
