/- GID: D5/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All-order golden beta gaps and the next finite exponent census. -/

import D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * Repository search found the frozen definition `o5Beta`, its closed form,
     and the public fourth-order census.  The latter supplies the exact value
     of beta seven and the predecessor census, so this module imports it
     directly rather than reproving that public result.
   * The predecessor's floor evaluations are private.  The new floor values
     and the all-order floor increment therefore have to be proved locally at
     the definition layer.  The closed form was checked but does not expose
     the discrete floor increment needed for the dichotomy.
   * Pinned Mathlib supplies `Int.floor_mono`, `Int.floor_add_intCast`,
     `Int.floor_eq_iff`, `Real.one_lt_goldenRatio`,
     `Real.goldenRatio_lt_two`, and `Real.goldenRatio_sq`.
   * This result is only an exponent-accounting theorem.  It asserts no local
     factor cancellation, analytic continuation, O-5 statement, or RH. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermNextExponentPattern

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus

noncomputable section

private theorem golden_floor_increment (v : Nat) :
    ⌊(((v + 2 : Nat) : Real) * Real.goldenRatio)⌋ -
          ⌊(((v + 1 : Nat) : Real) * Real.goldenRatio)⌋ = 1 ∨
      ⌊(((v + 2 : Nat) : Real) * Real.goldenRatio)⌋ -
          ⌊(((v + 1 : Nat) : Real) * Real.goldenRatio)⌋ = 2 := by
  let x : Real := ((v + 1 : Nat) : Real) * Real.goldenRatio
  have hnext : ((v + 2 : Nat) : Real) * Real.goldenRatio =
      x + Real.goldenRatio := by
    dsimp [x]
    push_cast
    ring
  have hlower : ⌊x⌋ + 1 <= ⌊x + Real.goldenRatio⌋ := by
    calc
      ⌊x⌋ + 1 = ⌊x + ((1 : Int) : Real)⌋ := by
        rw [Int.floor_add_intCast]
      _ <= ⌊x + Real.goldenRatio⌋ :=
        Int.floor_mono (by
          norm_num
          exact Real.one_lt_goldenRatio.le)
  have hupper : ⌊x + Real.goldenRatio⌋ <= ⌊x⌋ + 2 := by
    calc
      ⌊x + Real.goldenRatio⌋ <= ⌊x + ((2 : Int) : Real)⌋ :=
        Int.floor_mono (by
          norm_num
          exact Real.goldenRatio_lt_two.le)
      _ = ⌊x⌋ + 2 := by rw [Int.floor_add_intCast]
  rw [hnext]
  change ⌊x + Real.goldenRatio⌋ - ⌊x⌋ = 1 ∨
    ⌊x + Real.goldenRatio⌋ - ⌊x⌋ = 2
  omega

private theorem o5_beta_gap (v : Nat) :
    o5Beta (v + 1) - o5Beta v = Real.goldenRatio ∨
      o5Beta (v + 1) - o5Beta v = Real.goldenRatio ^ 2 := by
  rcases golden_floor_increment v with hone | htwo
  · left
    have honeReal :
        ((⌊(((v + 2 : Nat) : Real) * Real.goldenRatio)⌋ : Int) : Real) -
            ((⌊(((v + 1 : Nat) : Real) * Real.goldenRatio)⌋ : Int) : Real) = 1 := by
      exact_mod_cast hone
    rw [o5Beta, o5Beta]
    push_cast
    have honeReal' :
        ((⌊((v : Real) + 1 + 1) * Real.goldenRatio⌋ : Int) : Real) -
            ((⌊((v : Real) + 1) * Real.goldenRatio⌋ : Int) : Real) = 1 := by
      convert honeReal using 1
      rw [show (v : Real) + 1 + 1 = (v : Real) + 2 by ring]
      push_cast
      rfl
    nlinarith
  · right
    have htwoReal :
        ((⌊(((v + 2 : Nat) : Real) * Real.goldenRatio)⌋ : Int) : Real) -
            ((⌊(((v + 1 : Nat) : Real) * Real.goldenRatio)⌋ : Int) : Real) = 2 := by
      exact_mod_cast htwo
    rw [o5Beta, o5Beta, Real.goldenRatio_sq]
    push_cast
    have htwoReal' :
        ((⌊((v : Real) + 1 + 1) * Real.goldenRatio⌋ : Int) : Real) -
            ((⌊((v : Real) + 1) * Real.goldenRatio⌋ : Int) : Real) = 2 := by
      convert htwoReal using 1
      rw [show (v : Real) + 1 + 1 = (v : Real) + 2 by ring]
      push_cast
      rfl
    nlinarith

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

private theorem floor_nine_mul_goldenRatio :
    ⌊(9 : Real) * Real.goldenRatio⌋ = (14 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem floor_ten_mul_goldenRatio :
    ⌊(10 : Real) * Real.goldenRatio⌋ = (16 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem golden_cube :
    Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
  calc
    Real.goldenRatio ^ 3 =
        Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
      rw [Real.goldenRatio_sq]
    _ = 2 * Real.goldenRatio + 1 := by
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

private theorem golden_sixth :
    Real.goldenRatio ^ 6 = 8 * Real.goldenRatio + 5 := by
  calc
    Real.goldenRatio ^ 6 =
        Real.goldenRatio ^ 5 * Real.goldenRatio := by ring
    _ = (5 * Real.goldenRatio + 3) * Real.goldenRatio := by
      rw [golden_fifth]
    _ = 8 * Real.goldenRatio + 5 := by
      nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_eight :
    o5Beta 8 = Real.goldenRatio ^ 6 := by
  rw [o5Beta]
  norm_num
  rw [floor_nine_mul_goldenRatio, golden_sixth]
  ring

private theorem o5_beta_nine :
    o5Beta 9 = Real.goldenRatio ^ 6 + Real.goldenRatio ^ 2 := by
  rw [o5Beta]
  norm_num
  rw [floor_ten_mul_goldenRatio, golden_sixth]
  ring

private theorem o5_beta_seven :
    o5Beta 7 = Real.goldenRatio ^ 5 + Real.goldenRatio ^ 3 :=
  golden_germ_fourth_order_exponent_census.2.1

private theorem mixed_exponent_census_below_beta_seven :
    forall a b : Nat,
      (a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3 <= o5Beta 7 <->
        (b = 0 ∧ a <= 5) ∨
        (b = 1 ∧ a <= 4) ∨
        (b = 2 ∧ a <= 2) ∨
        (b = 3 ∧ a <= 1) := by
  intro a b
  rw [o5_beta_seven, Real.goldenRatio_sq, golden_cube, golden_fifth]
  constructor
  · intro hweight
    have ha : a <= 5 := by
      by_contra hnot
      have ha_six : 6 <= a := by omega
      have ha_cast : (6 : Real) <= (a : Real) := by exact_mod_cast ha_six
      have hb_nonneg : 0 <= (b : Real) := by positivity
      have hb_term :
          0 <= (b : Real) * (2 * Real.goldenRatio + 1) := by positivity
      have ha_term :
          6 * (Real.goldenRatio + 1) <=
            (a : Real) * (Real.goldenRatio + 1) :=
        mul_le_mul_of_nonneg_right ha_cast (by positivity)
      nlinarith [Real.goldenRatio_lt_two]
    have hb : b <= 3 := by
      by_contra hnot
      have hb_four : 4 <= b := by omega
      have hb_cast : (4 : Real) <= (b : Real) := by exact_mod_cast hb_four
      have ha_nonneg : 0 <= (a : Real) := by positivity
      have ha_term :
          0 <= (a : Real) * (Real.goldenRatio + 1) := by positivity
      nlinarith [Real.goldenRatio_pos]
    interval_cases a <;> interval_cases b <;>
      norm_num at * <;>
        nlinarith [Real.one_lt_goldenRatio,
          Real.goldenRatio_lt_two]
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
    · rcases hthree with ⟨rfl, ha⟩
      interval_cases a <;> norm_num at * <;>
        nlinarith [Real.one_lt_goldenRatio]

/-- Every consecutive golden beta gap is phi or phi-squared; beta eight and
beta nine give the next exact values and beta seven bounds the displayed
finite mixed-weight census. -/
theorem golden_germ_next_exponent_pattern :
    (forall v : Nat,
      o5Beta (v + 1) - o5Beta v = Real.goldenRatio ∨
        o5Beta (v + 1) - o5Beta v = Real.goldenRatio ^ 2) ∧
    o5Beta 8 = Real.goldenRatio ^ 6 ∧
    o5Beta 9 = Real.goldenRatio ^ 6 + Real.goldenRatio ^ 2 ∧
    o5Beta 7 < o5Beta 8 ∧
    o5Beta 8 < o5Beta 9 ∧
    (forall a b : Nat,
      (a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3 <= o5Beta 7 <->
        (b = 0 ∧ a <= 5) ∨
        (b = 1 ∧ a <= 4) ∨
        (b = 2 ∧ a <= 2) ∨
        (b = 3 ∧ a <= 1)) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  have hseven_lt_eight : o5Beta 7 < o5Beta 8 := by
    rcases o5_beta_gap 7 with hgap | hgap
    · nlinarith [Real.goldenRatio_pos]
    · nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have height_lt_nine : o5Beta 8 < o5Beta 9 := by
    rcases o5_beta_gap 8 with hgap | hgap
    · nlinarith [Real.goldenRatio_pos]
    · nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  exact ⟨o5_beta_gap, o5_beta_eight, o5_beta_nine,
    hseven_lt_eight, height_lt_nine,
    mixed_exponent_census_below_beta_seven⟩

#print axioms golden_germ_next_exponent_pattern

end

end D5.S3.Analytic.EulerGerm.GoldenGermNextExponentPattern
