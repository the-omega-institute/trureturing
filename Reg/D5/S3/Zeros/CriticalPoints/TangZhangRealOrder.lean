import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the full real-order resolution statement. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

open _root_.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
open _root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo (P)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n p => c n p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Only the constant in the first inequality is exposed; every other source clause is retained. -/
def arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 ≤ p →
       ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum ≤
         R.readout () n p * ∑ j, ‖z j‖ ^ (-p)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 < p →
       (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
         c n p * ∑ j, ‖z j‖ ^ (-p) ↔ ∀ i j, z i = z j)) ∧
    ¬ conjecture

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 1 (by omega) (fun _ => 1) (by intro j; norm_num) 1 (by norm_num)
  change ((Polynomial.derivative (P (fun _ : Fin 1 => (1 : ℂ)))).roots.map
    (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum ≤
      (-1 : ℝ) * ∑ _j : Fin 1, ‖(1 : ℂ)‖ ^ (-(1 : ℝ)) at hh
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
  norm_num [actual, realize, c, Real.rpow_two]

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n p => c n p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
    definition := some {
      owner := `D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
      name := `D5.S3.Zeros.CriticalPoints.TangZhangRealOrder.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
