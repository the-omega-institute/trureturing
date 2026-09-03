/- GID: D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourth-ledger golden exponent values and finite mixed-weight census. -/

import D5.S3.Analytic.GoldenEulerBeta
import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * This module reuses the frozen public definition `o5Beta` and the growth
     theorem `o5_beta_growth` from `GoldenEulerBeta`; that theorem is itself
     supplied there by the frozen closed form.  The frozen third-order ledger
     is imported as the direct ledger predecessor.
   * The predecessor's floor evaluations, beta-four/beta-five evaluations,
     and golden-fifth identity are private.  They cannot be referenced across
     the module boundary, so the needed floor and power calculations are
     rebuilt locally from `Real.goldenRatio_sq`.
   * The result is only an exponent census.  It supplies no signed fourth-order
     local factor and proves no fourth-order cancellation or analytic gain. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta

noncomputable section

private theorem goldenRatio_gt_eight_fifths :
    (8 : Real) / 5 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_five_thirds :
    Real.goldenRatio < (5 : Real) / 3 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_thirteen_eighths :
    Real.goldenRatio < (13 : Real) / 8 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem floor_six_mul_goldenRatio :
    ⌊(6 : Real) * Real.goldenRatio⌋ = (9 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem floor_seven_mul_goldenRatio :
    ⌊(7 : Real) * Real.goldenRatio⌋ = (11 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem floor_eight_mul_goldenRatio :
    ⌊(8 : Real) * Real.goldenRatio⌋ = (12 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_thirteen_eighths]

private theorem golden_cube :
    Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
  calc
    Real.goldenRatio ^ 3 =
        Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
      rw [Real.goldenRatio_sq]
    _ = 2 * Real.goldenRatio + 1 := by
      nlinarith [Real.goldenRatio_sq]

private theorem golden_fourth :
    Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
  calc
    Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
    _ = (Real.goldenRatio + 1) ^ 2 := by
      rw [Real.goldenRatio_sq]
    _ = 3 * Real.goldenRatio + 2 := by
      nlinarith [Real.goldenRatio_sq]

private theorem golden_fifth :
    Real.goldenRatio ^ 5 = 5 * Real.goldenRatio + 3 := by
  calc
    Real.goldenRatio ^ 5 =
        Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
    _ = (2 * Real.goldenRatio + 1) *
        (Real.goldenRatio + 1) := by
      rw [golden_cube, Real.goldenRatio_sq]
    _ = 5 * Real.goldenRatio + 3 := by
      nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_five :
    o5Beta 5 = Real.goldenRatio ^ 5 := by
  rw [o5Beta]
  norm_num
  rw [floor_six_mul_goldenRatio, golden_fifth]
  ring

private theorem o5_beta_six :
    o5Beta 6 = 2 * Real.goldenRatio ^ 4 := by
  rw [o5Beta]
  norm_num
  rw [floor_seven_mul_goldenRatio, golden_fourth]
  ring

private theorem o5_beta_seven :
    o5Beta 7 = Real.goldenRatio ^ 5 + Real.goldenRatio ^ 3 := by
  rw [o5Beta]
  norm_num
  rw [floor_eight_mul_goldenRatio, golden_fifth, golden_cube]
  ring

private theorem mixed_exponent_census_below_beta_six :
    forall a b : Nat,
      (a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3 <= o5Beta 6 <->
        (b = 0 ∧ a <= 5) ∨
        (b = 1 ∧ a <= 3) ∨
        (b = 2 ∧ a <= 2) ∨
        (b = 3 ∧ a = 0) := by
  intro a b
  rw [o5_beta_six, Real.goldenRatio_sq, golden_cube, golden_fourth]
  constructor
  · intro hweight
    have ha : a <= 5 := by
      by_contra hnot
      have ha_six : 6 <= a := by omega
      have ha_cast : (6 : Real) <= (a : Real) := by exact_mod_cast ha_six
      have hb_nonneg : 0 <= (b : Real) := by positivity
      nlinarith [Real.one_lt_goldenRatio]
    have hb : b <= 3 := by
      by_contra hnot
      have hb_four : 4 <= b := by omega
      have hb_cast : (4 : Real) <= (b : Real) := by exact_mod_cast hb_four
      have ha_nonneg : 0 <= (a : Real) := by positivity
      nlinarith [Real.one_lt_goldenRatio]
    interval_cases a <;> interval_cases b <;>
      norm_num at * <;> nlinarith [Real.one_lt_goldenRatio]
  · intro hcases
    rcases hcases with hzero | hone | htwo | hthree
    · rcases hzero with ⟨rfl, ha⟩
      interval_cases a <;> norm_num at * <;>
        nlinarith [Real.one_lt_goldenRatio]
    · rcases hone with ⟨rfl, ha⟩
      interval_cases a <;> norm_num at * <;>
        nlinarith [Real.one_lt_goldenRatio]
    · rcases htwo with ⟨rfl, ha⟩
      interval_cases a <;> norm_num at * <;>
        nlinarith [Real.one_lt_goldenRatio]
    · rcases hthree with ⟨rfl, rfl⟩
      norm_num
      nlinarith

/-- The next two golden Euler exponents and the finite fourth-ledger census.

The census includes the boundary collision `(a, b) = (2, 2)`, whose mixed
weight is exactly `o5Beta 6`.  It does not assert that any of these candidate
weights occurs in, or is cancelled by, a fourth-order local factor. -/
theorem golden_germ_fourth_order_exponent_census :
    o5Beta 6 = 2 * Real.goldenRatio ^ 4 ∧
      o5Beta 7 = Real.goldenRatio ^ 5 + Real.goldenRatio ^ 3 ∧
      o5Beta 5 < o5Beta 6 ∧
      o5Beta 6 < o5Beta 7 ∧
      Real.goldenRatio ^ 5 < o5Beta 6 ∧
      Real.goldenRatio ^ 5 < o5Beta 7 ∧
      (forall a b : Nat,
        (a : Real) * Real.goldenRatio ^ 2 +
            (b : Real) * Real.goldenRatio ^ 3 <= o5Beta 6 <->
          (b = 0 ∧ a <= 5) ∨
          (b = 1 ∧ a <= 3) ∨
          (b = 2 ∧ a <= 2) ∨
          (b = 3 ∧ a = 0)) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  have hfifth_lt_six : Real.goldenRatio ^ 5 < o5Beta 6 := by
    have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
    have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
    have hphi_inv :
        1 / Real.goldenRatio = Real.goldenRatio - 1 := by
      rw [one_div, Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    apply lt_of_lt_of_le _ (o5_beta_growth 6)
    rw [golden_fifth, hphi_inv]
    norm_num
    rw [Real.goldenRatio]
    nlinarith
  have hsix_lt_seven : o5Beta 6 < o5Beta 7 := by
    rw [o5_beta_six, o5_beta_seven, golden_fifth, golden_cube,
      golden_fourth]
    nlinarith [Real.one_lt_goldenRatio]
  refine ⟨o5_beta_six, o5_beta_seven, ?_, hsix_lt_seven,
    hfifth_lt_six, ?_, mixed_exponent_census_below_beta_six⟩
  · rw [o5_beta_five]
    exact hfifth_lt_six
  · exact lt_trans hfifth_lt_six hsix_lt_seven

#print axioms golden_germ_fourth_order_exponent_census

end

end D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus
