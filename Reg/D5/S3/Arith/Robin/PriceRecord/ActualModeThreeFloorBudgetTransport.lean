import D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source registration for the common coefficient in the literal floor error bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport

open LeanInformationAudit Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
  (delta jointSquare)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (d)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
  (boxSizes coordinates transportConstant floor_budget_errors)

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => transportConstant a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β a X ref w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
    37 / 50 ≤ β ∧ β < 3 / 4 → 0 < a → 2 ≤ log X → 1 + 2 / a ≤ log X →
    |log X - ref| ≤ 1 →
    jointSquare (boxSizes β a ref) h p (coordinates X) w ≤ 43 / 9 →
    let L := log X
    let K := R.readout () () a
    |(h : ℝ) * (L / d 2 X) - (p 0 : ℝ)| ≤ K * exp (-(L / 15)) ∧
    |(h : ℝ) * (d 3 X / d 2 X) - (p 1 : ℝ)| ≤ K * exp (-(L / 15)) / L ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpad : jointSquare (boxSizes (37 / 50) 1 3) 0 (fun _ => 0)
      (coordinates (exp 3)) 0 ≤ 43 / 9 := by
    simp [jointSquare, delta]
    norm_num
  have hbound := (h (β := 37 / 50) (a := 1) (X := exp 3) (ref := 3)
    (w := 0) (h := 0) (p := fun _ => 0) (by norm_num) (by norm_num)
    (by rw [log_exp]; norm_num) (by rw [log_exp]; norm_num)
    (by rw [log_exp]; norm_num) hpad).1
  have hneg : (-1 : ℝ) * exp (-(log (exp 3) / 15)) < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) (exp_pos _)
  exact (hneg.not_ge ((abs_nonneg _).trans hbound))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change transportConstant 1 ≠ transportConstant 2
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hnum : 0 < 64 * exp (1 / 15) * sqrt 43 := by positivity
  unfold transportConstant
  rw [mul_one]
  exact ne_of_gt (div_lt_div_of_pos_left hnum (by positivity) (by linarith only [hlog]))

def family : Registration arena (type_of% (@floor_budget_errors)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@floor_budget_errors, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@floor_budget_errors) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport.floor_budget_errors.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => transportConstant a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
