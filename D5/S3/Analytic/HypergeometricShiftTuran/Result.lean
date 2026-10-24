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
        (Real.Gamma (1 / 2 + t))⁻¹ ^ q := by
    simp [coeff, inv_pow]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have g2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have g3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have g32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have g52 : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have g72 : Real.Gamma (7 / 2) = 15 * Real.sqrt Real.pi / 8 := by
    rw [show (7 / 2 : ℝ) = ((3 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  -- the four Gamma arguments occurring in the first coefficient
  have e1 : (Real.Gamma 2)⁻¹ ^ q * (Real.Gamma 3)⁻¹ ^ q = (1 / 2 : ℝ) ^ q := by
    rw [g2, g3, ← mul_pow]; norm_num
  have e2 : (Real.Gamma (5 / 2))⁻¹ ^ q * (Real.Gamma (5 / 2))⁻¹ ^ q =
      (16 / (9 * Real.pi)) ^ q := by
    rw [← mul_pow, g52]
    congr 1
    field_simp
    nlinarith [hsq]
  have e3 : (Real.Gamma (3 / 2))⁻¹ ^ q * (Real.Gamma (7 / 2))⁻¹ ^ q =
      (16 / (15 * Real.pi)) ^ q := by
    rw [← mul_pow, g32, g72]
    congr 1
    field_simp
    nlinarith [hsq]
  have expand :
      turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
        1 (1 / 2) (1 / 2) 1 =
        ((Real.Gamma 2)⁻¹ ^ q * (Real.Gamma 3)⁻¹ ^ q -
            (Real.Gamma (3 / 2))⁻¹ ^ q * (Real.Gamma (7 / 2))⁻¹ ^ q) +
          ((Real.Gamma 3)⁻¹ ^ q * (Real.Gamma 2)⁻¹ ^ q -
            (Real.Gamma (5 / 2))⁻¹ ^ q * (Real.Gamma (5 / 2))⁻¹ ^ q) := by
    simp only [turanCoeff, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc,
      Nat.cast_zero, Nat.cast_one, Nat.sub_zero, Nat.sub_self, Nat.factorial_zero,
      Nat.factorial_one, mul_one, div_one, add_zero]
    norm_num
  rw [expand, mul_comm ((Real.Gamma 3)⁻¹ ^ q), e1, e2, e3]
  ring

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
