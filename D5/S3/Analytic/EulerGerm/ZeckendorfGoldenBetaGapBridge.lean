/- GID: D5/S3/Analytic/EulerGerm/ZeckendorfGoldenBetaGapBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least Zeckendorf digit selects the phi versus phi-squared consecutive golden beta gap. -/

import D5.S1.Words.ZeckendorfBeattyBridge
import D5.S3.Analytic.GoldenEulerBeta
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge

open D5.S0.Conventions
open D5.S3.Analytic.GoldenEulerBeta

private theorem floor_increment_eq_mechanical (v : ℕ) :
    ⌊(((v + 2 : ℕ) : ℝ) * Real.goldenRatio)⌋ -
        ⌊(((v + 1 : ℕ) : ℝ) * Real.goldenRatio)⌋ =
      2 - D5.S1.Words.goldenMechanicalLetter (v + 1) := by
  rw [D5.S1.Words.goldenMechanicalLetter]
  rw [D5.S1.Words.goldenMechanicalSlope, Real.inv_goldenRatio]
  rw [← Real.one_sub_goldenConj]
  have hphi : Real.goldenRatio - 1 = Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenConj]
  rw [← hphi]
  have hfloor (n : ℕ) :
      ⌊((n : ℝ) * (Real.goldenRatio - 1))⌋ =
        ⌊((n : ℝ) * Real.goldenRatio)⌋ - (n : ℤ) := by
    rw [mul_sub, mul_one, Int.floor_sub_intCast]
  rw [hfloor, hfloor]
  push_cast
  ring

/-- The least Zeckendorf digit gives an exact discrete address for the next
golden Euler-layer gap: absence selects the long phi-squared step, presence
the short phi step. -/
theorem zeckendorf_selects_golden_beta_gap (v : ℕ) :
    (2 ∉ wdigits v →
      o5Beta (v + 1) - o5Beta v = Real.goldenRatio ^ 2) ∧
    (2 ∈ wdigits v →
      o5Beta (v + 1) - o5Beta v = Real.goldenRatio) := by
  constructor
  · intro habsent
    have hletter : D5.S1.Words.goldenMechanicalLetter (v + 1) = 1 :=
      D5.S1.Words.zeckendorf_beatty_bridge v |>.mp habsent
    have hinc := floor_increment_eq_mechanical v
    rw [hletter] at hinc
    rw [o5Beta, o5Beta, Real.goldenRatio_sq]
    push_cast at *
    nlinarith
  · intro hpresent
    have hnotLetter : D5.S1.Words.goldenMechanicalLetter (v + 1) ≠ 1 := by
      intro hletter
      exact hpresent (D5.S1.Words.zeckendorf_beatty_bridge v |>.mpr hletter)
    have hletterZero : D5.S1.Words.goldenMechanicalLetter (v + 1) = 0 := by
      unfold D5.S1.Words.goldenMechanicalLetter
      have hslope : 0 < D5.S1.Words.goldenMechanicalSlope := by
        simp [D5.S1.Words.goldenMechanicalSlope]
        positivity
      have hslopeLt : D5.S1.Words.goldenMechanicalSlope < 1 := by
        rw [D5.S1.Words.goldenMechanicalSlope]
        exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
      have hbounds := Int.floor_add_one ((v + 1 : ℕ : ℝ) *
        D5.S1.Words.goldenMechanicalSlope)
      have hdiff :
          D5.S1.Words.goldenMechanicalLetter (v + 1) = 0 ∨
          D5.S1.Words.goldenMechanicalLetter (v + 1) = 1 := by
        rw [D5.S1.Words.goldenMechanicalLetter]
        have hx : (((v + 1 + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope) =
            ((v + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope +
              D5.S1.Words.goldenMechanicalSlope := by push_cast; ring
        rw [hx]
        have hlo := Int.floor_mono (show
          ((v + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope ≤
            ((v + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope +
              D5.S1.Words.goldenMechanicalSlope by linarith)
        have hhi := Int.floor_mono (show
          ((v + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope +
              D5.S1.Words.goldenMechanicalSlope <
            ((v + 1 : ℕ) : ℝ) * D5.S1.Words.goldenMechanicalSlope + 1 by linarith)
        rw [Int.floor_add_one] at hhi
        omega
      exact hdiff.resolve_right hnotLetter
    have hinc := floor_increment_eq_mechanical v
    rw [hletterZero] at hinc
    rw [o5Beta, o5Beta]
    push_cast at *
    nlinarith

#print axioms zeckendorf_selects_golden_beta_gap

end D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge
