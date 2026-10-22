/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Boundary
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Boundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.Analysis.Real.Pi.Bounds]
   utility: none
   digest: Strictly negative second coefficients of reciprocal Gamma Turanians at boundary shifts. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds

open D5.S3.Analytic.ReciprocalGammaTuran.Defs
open scoped BigOperators Real
namespace D5.S3.Analytic.ReciprocalGammaTuran.Boundary

private lemma half_gamma_square : Real.Gamma (1 / 2) ^ 2 = Real.pi := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 2)
  norm_num [show Real.pi * (1 / 2) = Real.pi / 2 by ring] at h
  nlinarith

/-- The second coefficient at the half shift has a closed form. -/
theorem d_two_half : turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) (1 / 2) 2 =
    1 - 10 / (3 * Real.pi) := by
  have h0 : Real.Gamma 0 = 0 := by simpa using Real.Gamma_neg_nat_eq_zero 0
  have h2 : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  have hn := Real.Gamma_add_one (s := -(1 / 2)) (by norm_num)
  have hp := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
  have hpp := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
  norm_num at hn hp hpp
  have hs := half_gamma_square
  have hg : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hneg : Real.Gamma (-(1 / 2)) = -2 * Real.Gamma (1 / 2) := by linarith
  have hpos : Real.Gamma (3 / 2) = Real.Gamma (1 / 2) / 2 := by linarith
  have hpos2 : Real.Gamma (5 / 2) = 3 * Real.Gamma (1 / 2) / 4 := by rw [hpos] at hpp; linarith
  norm_num [turanCoeff, Finset.sum_range_succ, rgamma, h0, h2, hneg, hpos, hpos2,
    Real.Gamma_one]
  field_simp
  nlinarith

/-- The half-shift coefficient is strictly negative. -/
theorem d_two_half_neg : turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) (1 / 2) 2 < 0 := by
  rw [d_two_half]
  have hp := Real.pi_pos
  have hb := Real.pi_lt_d2
  apply sub_neg.mpr
  apply (lt_div_iff₀ (by positivity : 0 < 3 * Real.pi)).2
  linarith
end D5.S3.Analytic.ReciprocalGammaTuran.Boundary
