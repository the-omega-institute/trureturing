/- GID: D5/S3/Analytic/HypergeometricShiftTuran/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/Result.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim
   digest: Negative first coefficients for every denominator multiplicity at least six. -/

/-
# Negative first coefficient of the shifted Turanian

admission_basis: open-problem-resolution (#20878; Refuted)
escape_witness: none
Direct frozen dependencies: none (the only D5 import is Defs from the same delivery; the
other imports are pinned Mathlib).

Per-declaration proof_shape:
* first_coefficient_eq: bind-only; consumers: half_parameter_family_neg.
* half_parameter_family_neg: bind-only; consumers: result.
* result: bind-only; external conjecture settlement #20878.
Each row has escape_witness: none and Direct frozen dependencies: none.
The definitions coeff, turanCoeff, esymm, cond13 and claim of Defs are used by result.
Shared bind-only helpers and their consumers:
* Defs.gamma_three_halves: Defs.gamma_three_seven_halves_inv_pow_mul.
* Defs.gamma_five_halves: Defs.gamma_five_halves_inv_pow_mul,
  TwoBlockResult.first_coefficient_eq.
* Defs.gamma_seven_halves: Defs.gamma_three_seven_halves_inv_pow_mul,
  TwoBlockResult.first_coefficient_eq.
* Defs.gamma_five_halves_inv_pow_mul: first_coefficient_eq,
  TwoBlockResult.first_coefficient_eq.
* Defs.gamma_three_seven_halves_inv_pow_mul: first_coefficient_eq,
  TwoBlockResult.first_coefficient_eq.
* Defs.pi_base_bound: half_parameter_family_neg, TwoBlockResult.half_parameter_family_neg.
* Defs.gamma_three: Defs.gamma_two_three_inv_pow_mul, TwoBlockResult.first_coefficient_eq.
* Defs.gamma_two_three_inv_pow_mul: Result.first_coefficient_eq, TwoBlockResult.first_coefficient_eq.
* Defs.base_pow_mul_half_pow: Result.half_parameter_family_neg,
  TwoBlockResult.half_parameter_family_neg.
All nine shared helpers have proof_shape: bind-only and escape_witness: none.
Escape audit unfinished for the public helpers: https://github.com/the-omega-institute/trureturing/issues/20966
The decisive Mathlib facts are Real.Gamma_two (through Defs), Real.Gamma_nat_eq_factorial,
pow_le_pow_left₀ and pow_le_pow_right₀.
The module certifies one explicit parameter instance that refutes Defs.claim, so the
utility kind is certified-instance with basis refutes.
-/

import D5.S3.Analytic.HypergeometricShiftTuran.Defs

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
  have e1 := gamma_two_three_inv_pow_mul q
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
  rw [expand, mul_comm ((Real.Gamma 3)⁻¹ ^ q), e1, gamma_five_halves_inv_pow_mul,
    gamma_three_seven_halves_inv_pow_mul]
  ring

/-- Every denominator multiplicity at least six gives a negative first
coefficient at the positive half shifts and the unit base parameter. -/
theorem half_parameter_family_neg (q : ℕ) (hq : 6 ≤ q) :
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 < 0 := by
  have hbase := Defs.pi_base_bound
  have hone : (1 : ℝ) ≤ 32 / (9 * Real.pi) := by
    linarith
  have hsix : (2 : ℝ) < (32 / (9 * Real.pi)) ^ 6 := by
    calc
      (2 : ℝ) < (640 / 567 : ℝ) ^ 6 := by norm_num
      _ ≤ (32 / (9 * Real.pi)) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) hbase.le 6
  have hpower : (2 : ℝ) < (32 / (9 * Real.pi)) ^ q :=
    hsix.trans_le (pow_le_pow_right₀ hone hq)
  have hfactor := base_pow_mul_half_pow q
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
