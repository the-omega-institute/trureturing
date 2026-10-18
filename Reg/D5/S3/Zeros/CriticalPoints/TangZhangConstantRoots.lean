import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the coefficient in the coincident-root moment formula. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots

open _root_.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
open _root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo (P)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n p => (((n : ℝ) + 1) ^ p + n - 1) / n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n) (a : ℂ) (ha : a ≠ 0) (p : ℝ),
    ((Polynomial.derivative (P (fun _ : Fin n => a))).roots.map
      (fun w => ‖w‖ ^ (-p))).sum =
        R.readout () n p * ∑ _ : Fin n, ‖a‖ ^ (-p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by omega) 1 one_ne_zero 1
  change ((Polynomial.derivative (P (fun _ : Fin 1 => (1 : ℂ)))).roots.map
    (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
      (-1 : ℝ) * ∑ _ : Fin 1, ‖(1 : ℂ)‖ ^ (-(1 : ℝ)) at hh
  simp only [Fin.sum_univ_one, norm_one, Real.one_rpow, mul_one] at hh
  have hnonneg : 0 ≤ ((Polynomial.derivative (P (fun _ : Fin 1 => (1 : ℂ)))).roots.map
      (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum := Multiset.sum_nonneg (by
    intro x hx
    obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.rpow_nonneg (norm_nonneg w) _)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [actual, realize, Real.rpow_two]

def source_registration : Registration arena (type_of% @constant_roots_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨constant_roots_moment, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots.constant_roots_moment)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n p => (((n : ℝ) + 1) ^ p + n - 1) / n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
