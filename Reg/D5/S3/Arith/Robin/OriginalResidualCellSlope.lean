import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualCellSlope
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Finset
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open _root_.D5.S3.Arith.Robin.OriginalResidualCellSlope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualCellSlope

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s =>
    |reciprocalPrefix p.1 p.1| * weight s.1 / 8 +
      (cellMass s.1 s.2 / 2) * rho p.1 (p.2 + 1) *
        (Real.log ((p.1 : ℝ) / (p.2 + 1 : ℕ)) +
          (Real.log ((p.1 : ℝ) / (p.2 + 1 : ℕ))) ^ 2 / 2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N - 2 →
    ∀ {a b : ℝ}, (N : ℝ) < a → a < b → b < 2 * (N : ℝ) →
    reciprocalPrefix N N - reciprocalPrefix N q +
        (mobiusPrefix q + 2) * logKernel N (q + 1 : ℕ) = abelTail N (q + 1) ∧
    weightedTail N (q + 1) = Real.log ((N : ℝ) / (q + 1 : ℕ)) +
      ∑ k ∈ Finset.Ico (q + 2) N, logKernel N k ∧
    (Real.log ((N : ℝ) / (q + 1 : ℕ)) ≤ weightedTail N (q + 1) ∧
      weightedTail N (q + 1) ≤ Real.log ((N : ℝ) / (q + 1 : ℕ)) +
        (Real.log ((N : ℝ) / (q + 1 : ℕ))) ^ 2 / 2) ∧
    (∀ k ∈ Finset.Ico (q + 1) N, |mobiusPrefix k + 2| ≤ rho N (q + 1) * k) ∧
    |discrepancy N q a b| ≤ R.readout () (N, q) (a, b) ∧
    (phaseCentre N a b + (cellMass a b / 2) * alpha N (q + 1) * weightedTail N (q + 1) -
        |reciprocalPrefix N N| * (weight a - weight b) / 16 ≤ discrepancy N q a b ∧
      discrepancy N q a b ≤ phaseCentre N a b +
        (cellMass a b / 2) * beta N (q + 1) * weightedTail N (q + 1) +
          |reciprocalPrefix N N| * (weight a - weight b) / 16)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (N := 3) (q := 0) (by norm_num) (by norm_num)
    (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num)).2.2.2.2.1
  change |discrepancy 3 0 4 5| ≤ -1 at he
  linarith [abs_nonneg (discrepancy 3 0 4 5)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2, 0), (0, 0), (2, 2), ?_⟩
  have hU : reciprocalPrefix 2 2 = Real.log 2 := by
    norm_num [reciprocalPrefix, sum_Ioc_succ_top, logKernel]
  have hw : weight 0 = 0 := by simp [weight]
  have hp := _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment.weight_pos
    (show (1 : ℝ) < 2 by norm_num)
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simp only [actual, realize, cellMass, intervalIntegral.integral_same, hU,
    abs_of_pos hl, hw, mul_zero, zero_div, zero_mul, add_zero]
  positivity

def family : Registration arena (type_of% (@cell_slope_payment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cell_slope_payment, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cell_slope_payment) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalResidualCellSlope.cell_slope_payment.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualCellSlope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.Robin.OriginalResidualCellSlope
