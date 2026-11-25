/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortQuadrature/CompactShortMomentTable
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-denominator centered moments for short-gap Taylor evaluation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactCenteredMomentCertificate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortQuadrature.CompactShortMomentData
import Mathlib.Tactic.IntervalCases

/-! # The short-gap centered moment table -/

namespace RefinedBMV.PositiveCenter.CompactShortMomentTable

open SmallCorner (momentHorner normalizedMomentCoeffs certifiedMomentCoeffs certifiedMomentCoeffs_eq)
open CenteredMomentCertificate (eval rowLhs rowRhs rows_eval tiltedCoefficients tiltedCoefficients_eval)
open private integerSplitPlusOne integerSplitPlusOne_scaled scaledIntegers
  coeffScale_scaledIntegers horner_scale horner_split from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

open private denominator table from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortQuadrature.CompactShortMomentData

private def row (n : ℕ) : List ℤ := table[n]?.getD []

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
-- Check the integer polynomial identity at each of the 49 orders.
private theorem row_valid (m : ℕ) (hm : m ≤ 48) :
    rowLhs row m = rowRhs denominator m := by
  interval_cases m <;> decide +kernel

/-- Exact Taylor coefficients using the integer table within its certified range. -/
def coefficients (j n : ℕ) : List ℚ :=
  if j + n ≤ 48 then tiltedCoefficients row denominator j n
  else compactTiltedMomentCoefficients j n

/-- The table and the existing representation agree on the grid spacings. -/
theorem coefficients_eval {p : ℕ} (hp : 0 < p) (j n : ℕ) :
    let h := 3 / (p : ℝ)
    momentHorner h (coefficients j n) =
      compactPositiveMomentCoefficient h j n / (n.factorial : ℝ) := by
  by_cases hjn : j + n ≤ 48
  · have hD : denominator ≠ 0 := by decide +kernel
    simpa only [coefficients, ite_eq_left hjn] using tiltedCoefficients_eval row_valid hD hp j n hjn
  · intro h
    rw [coefficients, ite_eq_right hjn, compactTiltedMomentCoefficients_eval]

private def marginalScale (m : ℕ) : ℚ :=
  4 * (-1 : ℚ) ^ m / ((denominator : ℚ) * (m.factorial : ℚ))

/-- Normalized marginal Taylor coefficients from the quotient of the centered moment row. -/
def marginalCoefficients (m : ℕ) : List ℚ :=
  if 2 ≤ m ∧ m ≤ 48 then
    scaledIntegers (marginalScale m) (integerSplitPlusOne (row m)).2
  else certifiedMomentCoeffs 0 m

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem marginal_remainder_zero (m : ℕ) (hlo : 2 ≤ m) (hhi : m ≤ 48) :
    (integerSplitPlusOne (row m)).1 = 0 := by
  interval_cases m <;> decide +kernel

/-- Horner evaluation of the table quotient gives the existing normalized moment at spacing 3/p. -/
theorem marginalCoefficients_eval {p : ℕ} (hp : 0 < p) (m : ℕ) :
    momentHorner (3 / (p : ℝ)) (marginalCoefficients m) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 m) := by
  by_cases hm : 2 ≤ m ∧ m ≤ 48
  · let h : ℝ := 3 / (p : ℝ)
    let d : ℚ := marginalScale m
    have hs : momentHorner h (scaledIntegers d (row m)) = (d : ℝ) * eval h (row m) := by
      simpa only [mul_one, horner_scale, eval] using
        (congrArg (momentHorner h) (coeffScale_scaledIntegers d 1 (row m))).symm
    have hsplit := horner_split h (scaledIntegers d (row m))
    simp only [integerSplitPlusOne_scaled, marginal_remainder_zero m hm.1 hm.2,
      Int.cast_zero, zero_mul, Rat.cast_zero, zero_add] at hsplit
    rw [hs, rows_eval row_valid hp m hm.2] at hsplit
    have hmoment : compactCenteredMomentPolynomial h m =
        ((1 + h) / 4) * (m.factorial : ℝ) * momentHorner h (normalizedMomentCoeffs 0 m) := by
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
      rfl
    have hD : (denominator : ℝ) ≠ 0 := by
      exact_mod_cast (show denominator ≠ 0 by decide +kernel)
    have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
    have hh : 1 + h ≠ 0 := by
      dsimp [h]
      positivity
    have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hscale :
        (d : ℝ) * (denominator : ℝ) * (-1 : ℝ) ^ m * ((1 + h) / 4) * (m.factorial : ℝ) =
          1 + h := by
      simp only [d, marginalScale, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
      calc
        _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (1 + h) := by
          field_simp [hD, hfac] <;> ring
        _ = _ := by rw [hsign, one_mul]
    rw [marginalCoefficients, if_pos hm]
    apply mul_left_cancel₀ hh
    calc
      _ = (d : ℝ) * ((denominator : ℝ) * ((-1 : ℝ) ^ m *
            compactCenteredMomentPolynomial h m)) := hsplit.symm
      _ = ((d : ℝ) * (denominator : ℝ) * (-1 : ℝ) ^ m * ((1 + h) / 4) * (m.factorial : ℝ)) *
            momentHorner h (normalizedMomentCoeffs 0 m) := by rw [hmoment]; ring
      _ = _ := by rw [hscale]
  · rw [marginalCoefficients, if_neg hm, certifiedMomentCoeffs_eq]

end RefinedBMV.PositiveCenter.CompactShortMomentTable
