import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t β => moment t β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t β : ℝ}, 4 ≤ t → 0 ≤ β →
    |R.readout () t β - t ^ (1 / 2 - β) / 2| ≤
      (4 + β + 2 * β * 2 ^ (β + 1)) * t ^ (-1 / 5 : ℝ) *
        (t ^ (1 / 2 - β) / 2)

private lemma test_scale : (32768 : ℝ) ^ (-1 / 5 : ℝ) = 1 / 8 := by
  calc
    _ = ((8 : ℝ) ^ 5) ^ (-1 / 5 : ℝ) := by norm_num
    _ = (8 : ℝ) ^ ((5 : ℝ) * (-1 / 5 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    _ = _ := by norm_num [Real.rpow_neg_one]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (t := 32768) (β := 0) (by norm_num) (by norm_num)
  change |0 - (32768 : ℝ) ^ (1 / 2 - 0) / 2| ≤ _ at ht
  simp only [sub_zero, zero_sub, abs_neg, zero_mul, add_zero,
    test_scale, abs_of_pos (by positivity : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) / 2)] at ht
  have hp : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨32768, 0, 1, ?_⟩
  change moment 32768 0 ≠ moment 32768 1
  have h0 := original_window_moment_estimate (t := 32768) (β := 0)
    (by norm_num) (by norm_num)
  have h1 := original_window_moment_estimate (t := 32768) (β := 1)
    (by norm_num) (by norm_num)
  rw [test_scale] at h0 h1
  norm_num only [sub_zero, zero_mul, add_zero, one_mul,
    show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h0 h1
  have hs : (32768 : ℝ) ^ (-(1 / 2 : ℝ)) = (32768 : ℝ) ^ (1 / 2 : ℝ) / 32768 := by
    calc
      _ = (32768 : ℝ) ^ ((1 / 2 : ℝ) - 1) := by norm_num
      _ = _ := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 32768), Real.rpow_one]
  rw [hs] at h1
  have hp : 0 < (32768 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hlow := (abs_le.mp h0).1
  have hhigh := (abs_le.mp h1).2
  intro heq
  rw [heq] at hlow
  norm_num at hlow hhigh
  linarith

def family : Registration arena (type_of% (@original_window_moment_estimate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_window_moment_estimate, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_window_moment_estimate)
    (type_of% (realize signature (fun _ t β => moment t β) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalMovingWindowMoment.original_window_moment_estimate.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t β => moment t β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalMovingWindowMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.OriginalMovingWindowMoment
