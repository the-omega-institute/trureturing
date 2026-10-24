/- GID: D5/S3/Analytic/HypergeometricShiftTuran/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/Result.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim
   digest: Negative first coefficients for every denominator multiplicity at least six refute the universal coefficient assertion. -/

import D5.S3.Analytic.HypergeometricShiftTuran.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open scoped BigOperators
open D5.S3.Analytic.HypergeometricShiftTuran.Defs

namespace D5.S3.Analytic.HypergeometricShiftTuran.Result

private lemma first_coefficient_eq (q : ℕ) :
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 =
      2 * (1 / 2 : ℝ) ^ q - (16 / (9 * Real.pi)) ^ q -
        (16 / (15 * Real.pi)) ^ q := by
  have hc (t : ℝ) :
      coeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ)) t =
        (1 / Real.Gamma (1 / 2 + t)) ^ q := by
    simp [coeff, div_pow]
  have htwo := Real.Gamma_nat_eq_factorial 1
  have hthree := Real.Gamma_nat_eq_factorial 2
  norm_num at htwo hthree
  have hhalf1 := Real.Gamma_nat_add_half 1
  have hhalf2 := Real.Gamma_nat_add_half 2
  have hhalf3 := Real.Gamma_nat_add_half 3
  norm_num [Nat.doubleFactorial] at hhalf1 hhalf2 hhalf3
  have hsquare := Real.sq_sqrt Real.pi_pos.le
  have hpair1 : Real.Gamma (5 / 2) * Real.Gamma (5 / 2) =
      9 * Real.pi / 16 := by
    rw [hhalf2]
    nlinarith [hsquare]
  have hpair2 : Real.Gamma (3 / 2) * Real.Gamma (7 / 2) =
      15 * Real.pi / 16 := by
    rw [hhalf1, hhalf3]
    nlinarith [hsquare]
  calc
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
        1 (1 / 2) (1 / 2) 1 =
        ((1 / Real.Gamma 2) ^ q * (1 / Real.Gamma 3) ^ q -
          (1 / Real.Gamma (3 / 2)) ^ q * (1 / Real.Gamma (7 / 2)) ^ q) +
        ((1 / Real.Gamma 3) ^ q * (1 / Real.Gamma 2) ^ q -
          (1 / Real.Gamma (5 / 2)) ^ q * (1 / Real.Gamma (5 / 2)) ^ q) := by
      norm_num [turanCoeff, Finset.sum_range_succ, hc]
    _ = 2 * (1 / 2 : ℝ) ^ q -
        ((1 / Real.Gamma (5 / 2)) * (1 / Real.Gamma (5 / 2))) ^ q -
        ((1 / Real.Gamma (3 / 2)) * (1 / Real.Gamma (7 / 2))) ^ q := by
      simp only [htwo, hthree, div_one, one_pow, one_mul, mul_one, mul_pow]
      ring
    _ = 2 * (1 / 2 : ℝ) ^ q - (16 / (9 * Real.pi)) ^ q -
        (16 / (15 * Real.pi)) ^ q := by
      rw [div_mul_div_comm, div_mul_div_comm, one_mul, hpair1, hpair2]
      norm_num [one_div_div]

/-- Every denominator multiplicity at least six gives a negative first
coefficient at the positive half shifts and the unit base parameter. -/
theorem half_parameter_family_neg (q : ℕ) (hq : 6 ≤ q) :
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 < 0 := by
  have hbase : (640 / 567 : ℝ) < 32 / (9 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity : 0 < 9 * Real.pi)).2
    nlinarith [Real.pi_lt_d2]
  have hone : (1 : ℝ) ≤ 32 / (9 * Real.pi) := by
    linarith
  have hsix : (2 : ℝ) < (32 / (9 * Real.pi)) ^ 6 := by
    calc
      (2 : ℝ) < (640 / 567 : ℝ) ^ 6 := by norm_num
      _ ≤ (32 / (9 * Real.pi)) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) hbase.le 6
  have hpower : (2 : ℝ) < (32 / (9 * Real.pi)) ^ q :=
    hsix.trans_le (pow_le_pow_right₀ hone hq)
  have hfactor : (32 / (9 * Real.pi)) ^ q * (1 / 2 : ℝ) ^ q =
      (16 / (9 * Real.pi)) ^ q := by
    rw [← mul_pow]
    congr 1
    ring
  have hleading := mul_lt_mul_of_pos_right hpower
    (by positivity : 0 < (1 / 2 : ℝ) ^ q)
  rw [hfactor] at hleading
  have htail : (0 : ℝ) < (16 / (15 * Real.pi)) ^ q := by positivity
  rw [first_coefficient_eq]
  linarith

/-- The universal coefficient nonnegativity assertion is false. -/
theorem result : ¬ Defs.claim := by
  intro hclaim
  have hnonneg := hclaim 0 6 (fun _ : Fin 0 => 0) (fun _ : Fin 6 => (1 / 2 : ℝ))
    (by norm_num) (by intro i; exact Fin.elim0 i) (by intro j; norm_num)
    (by intro j hj; exact (Nat.not_lt_zero j hj).elim)
    1 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1
  exact (not_lt_of_ge hnonneg) (half_parameter_family_neg 6 (by norm_num))

end D5.S3.Analytic.HypergeometricShiftTuran.Result
