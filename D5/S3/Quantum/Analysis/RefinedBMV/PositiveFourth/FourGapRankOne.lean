/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FourGapRankOne
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three-node finite difference of the uniform four-gap kernel is rank one. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourGapPowerSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! A common resolvent relation cancels the complete homogeneous part of the
three-node difference and leaves a product of the two unchanged slot factors. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

open private linearDenominator
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourGapPowerSeries
open private FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

private theorem pole_pair_relation (a b c : ℝ) :
    PowerSeries.C (c - a) * (pole a 1 * pole c 1) =
      PowerSeries.C (b - a) * (pole a 1 * pole b 1) +
        PowerSeries.C (c - b) * (pole b 1 * pole c 1) := by
  let P := pole a 1 * pole b 1 * pole c 1
  have ha : pole a 1 * linearDenominator a = 1 := by
    simpa only [pow_one] using pole_mul_denominator a 1
  have hb : pole b 1 * linearDenominator b = 1 := by
    simpa only [pow_one] using pole_mul_denominator b 1
  have hc : pole c 1 * linearDenominator c = 1 := by
    simpa only [pow_one] using pole_mul_denominator c 1
  have hP (x : ℝ) :
      P * linearDenominator x =
        pole a 1 * pole b 1 * pole c 1 * linearDenominator x := rfl
  have hPa : P * linearDenominator a = pole b 1 * pole c 1 := by
    rw [hP, show pole a 1 * pole b 1 * pole c 1 * linearDenominator a =
      pole b 1 * pole c 1 * (pole a 1 * linearDenominator a) by ring, ha, mul_one]
  have hPb : P * linearDenominator b = pole a 1 * pole c 1 := by
    rw [hP, show pole a 1 * pole b 1 * pole c 1 * linearDenominator b =
      pole a 1 * pole c 1 * (pole b 1 * linearDenominator b) by ring, hb, mul_one]
  have hPc : P * linearDenominator c = pole a 1 * pole b 1 := by
    rw [hP, mul_assoc, hc, mul_one]
  have hden :
      PowerSeries.C (c - a) * linearDenominator b =
        PowerSeries.C (b - a) * linearDenominator c +
          PowerSeries.C (c - b) * linearDenominator a := by
    simp only [linearDenominator, map_sub]
    ring
  rw [← hPb, ← hPc, ← hPa]
  linear_combination P * hden

/-- Dividing this identity by the positive outer interval shows that
interpolating two slots introduces a rank-one correction in the other slots. -/
theorem gapDefect_pair_difference (p : ℕ) (a b c u v : ℝ) :
    let e := (p : ℝ) / 4
    (c - a) * FourCopyGap.gapDefect p u v a c
      - (b - a) * FourCopyGap.gapDefect p u v a b
      - (c - b) * FourCopyGap.gapDefect p u v b c =
      u ^ e * v ^ e * (FourCopyGap.gaps p).card *
        ((b - a) * (a ^ e * b ^ e) + (c - b) * (b ^ e * c ^ e)
          - (c - a) * (a ^ e * c ^ e)) := by
  have hcoeff (d x y : ℝ) :
      PowerSeries.coeff p (pole u 1 * (pole v 1 * (PowerSeries.C d *
          (pole x 1 * pole y 1)))) =
        d * PowerSeries.coeff p (pole u 1 * (pole v 1 * (pole x 1 * pole y 1))) := by
    rw [show pole u 1 * (pole v 1 * (PowerSeries.C d * (pole x 1 * pole y 1))) =
      PowerSeries.C d * (pole u 1 * (pole v 1 * (pole x 1 * pole y 1))) by ring,
      PowerSeries.coeff_C_mul]
  have h := congrArg (fun P : Series =>
    PowerSeries.coeff p (pole u 1 * (pole v 1 * P))) (pole_pair_relation a b c)
  simp only [mul_add, map_add, hcoeff] at h
  simp only [gapDefect_eq_coeff_poles, FourCopyGap.balanced]
  linear_combination h

/-- The coefficient of the rank-one correction is strictly positive at
ordered positive nodes and a positive exponent. -/
theorem pair_geometric_residual_pos {a b c e : ℝ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (he : 0 < e) :
    0 < (b - a) * (a ^ e * b ^ e) + (c - b) * (b ^ e * c ^ e)
      - (c - a) * (a ^ e * c ^ e) := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hca : 0 < c - a := sub_pos.mpr (hab.trans hbc)
  let s := (c - b) / (c - a)
  let t := (b - a) / (c - a)
  have hs : 0 < s := div_pos (sub_pos.mpr hbc) hca
  have ht : 0 < t := div_pos (sub_pos.mpr hab) hca
  have hst : s + t = 1 := by
    dsimp [s, t]
    field_simp [hca.ne']
    ring
  have hmean : s * a + t * c = b := by
    dsimp [s, t]
    field_simp [hca.ne']
    ring
  have hlog := Real.strictConcaveOn_log_Ioi.2 ha hc (ne_of_lt (hab.trans hbc)) hs ht hst
  change s * Real.log a + t * Real.log c < Real.log (s * a + t * c) at hlog
  rw [hmean] at hlog
  have harg : Real.log b * (-e) <
      s * (Real.log a * (-e)) + t * (Real.log c * (-e)) := by
    simpa only [add_mul, mul_assoc] using mul_lt_mul_of_neg_right hlog (neg_lt_zero.mpr he)
  have hconv := Real.convexOn_exp.2 (Set.mem_univ (Real.log a * (-e)))
    (Set.mem_univ (Real.log c * (-e))) hs.le ht.le hst
  have hpow : b ^ (-e) < s * a ^ (-e) + t * c ^ (-e) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hc]
    exact lt_of_lt_of_le (Real.exp_lt_exp.mpr harg) hconv
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, Real.rpow_neg hc.le] at hpow
  have hap := Real.rpow_pos_of_pos ha e
  have hbp := Real.rpow_pos_of_pos hb e
  have hcp := Real.rpow_pos_of_pos hc e
  have hscaled := mul_lt_mul_of_pos_left hpow
    (show 0 < (c - a) * (a ^ e * b ^ e * c ^ e) by positivity)
  apply sub_pos.mpr
  dsimp [s, t] at hscaled
  convert hscaled using 1 <;>
    field_simp [hca.ne', hap.ne', hbp.ne', hcp.ne'] <;> ring

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
