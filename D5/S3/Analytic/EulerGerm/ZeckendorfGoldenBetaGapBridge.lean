/- GID: D5/S3/Analytic/EulerGerm/ZeckendorfGoldenBetaGapBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least Zeckendorf digit selects the two consecutive golden beta gaps. -/

import D5.S1.Words.ZeckendorfBeattyBridge
import D5.S3.Analytic.EulerGerm.GoldenGermNextExponentPattern
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge

open D5.S0.Conventions
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenGermNextExponentPattern

/-- The golden floor increment is one plus the shifted mechanical letter. -/
private theorem floor_increment_eq_one_add_mechanical (v : ℕ) :
    ⌊(((v + 2 : ℕ) : ℝ) * Real.goldenRatio)⌋ -
        ⌊(((v + 1 : ℕ) : ℝ) * Real.goldenRatio)⌋ =
      1 + D5.S1.Words.goldenMechanicalLetter (v + 1) := by
  unfold D5.S1.Words.goldenMechanicalLetter
  unfold D5.S1.Words.goldenMechanicalSlope
  have hInv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenConj]
  rw [hInv]
  have hfloor (n : ℕ) :
      ⌊((n : ℝ) * (Real.goldenRatio - 1))⌋ =
        ⌊((n : ℝ) * Real.goldenRatio)⌋ - (n : ℤ) := by
    rw [mul_sub, mul_one]
    convert Int.floor_sub_intCast
      ((n : ℝ) * Real.goldenRatio) (n : ℤ) using 1 <;> norm_num
  rw [hfloor, hfloor]
  push_cast
  ring

/-- Exact real-valued bridge from the shifted mechanical letter to the next
consecutive golden Euler exponent gap. -/
private theorem beta_gap_eq_golden_add_mechanical (v : ℕ) :
    o5Beta (v + 1) - o5Beta v =
      Real.goldenRatio +
        (D5.S1.Words.goldenMechanicalLetter (v + 1) : ℝ) := by
  have hinc := floor_increment_eq_one_add_mechanical v
  have hincReal :
      ((⌊(((v + 2 : ℕ) : ℝ) * Real.goldenRatio)⌋ : ℤ) : ℝ) -
          ((⌊(((v + 1 : ℕ) : ℝ) * Real.goldenRatio)⌋ : ℤ) : ℝ) =
        1 + (D5.S1.Words.goldenMechanicalLetter (v + 1) : ℝ) := by
    exact_mod_cast hinc
  calc
    o5Beta (v + 1) - o5Beta v =
        ((⌊(((v + 2 : ℕ) : ℝ) * Real.goldenRatio)⌋ : ℤ) : ℝ) -
          ((⌊(((v + 1 : ℕ) : ℝ) * Real.goldenRatio)⌋ : ℤ) : ℝ) +
            (Real.goldenRatio - 1) := by
              rw [o5Beta, o5Beta]
              push_cast
              ring
    _ = (1 +
          (D5.S1.Words.goldenMechanicalLetter (v + 1) : ℝ)) +
            (Real.goldenRatio - 1) := by rw [hincReal]
    _ = Real.goldenRatio +
          (D5.S1.Words.goldenMechanicalLetter (v + 1) : ℝ) := by ring

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
      (D5.S1.Words.zeckendorf_beatty_bridge v).mp habsent
    rw [beta_gap_eq_golden_add_mechanical, hletter]
    norm_num [Real.goldenRatio_sq]
  · intro hpresent
    have hnotLetter : D5.S1.Words.goldenMechanicalLetter (v + 1) ≠ 1 := by
      intro hletter
      have habsent : 2 ∉ wdigits v :=
        (D5.S1.Words.zeckendorf_beatty_bridge v).mpr hletter
      exact habsent hpresent
    rcases golden_germ_next_exponent_pattern.1 v with hshort | hlong
    · exact hshort
    · have hformula := beta_gap_eq_golden_add_mechanical v
      rw [hlong, Real.goldenRatio_sq] at hformula
      have hletterReal :
          (D5.S1.Words.goldenMechanicalLetter (v + 1) : ℝ) = 1 := by
        nlinarith
      have hletter : D5.S1.Words.goldenMechanicalLetter (v + 1) = 1 := by
        exact_mod_cast hletterReal
      exact (hnotLetter hletter).elim

#print axioms zeckendorf_selects_golden_beta_gap

end D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge
