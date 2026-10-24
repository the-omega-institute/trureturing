/- GID: D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs.claim
   digest: A shifted numerator gives negative first coefficients for all multiplicities at least seven. -/

/-
# Negative first coefficients for the two-block hypergeometric Turanian

admission_basis: open-problem-resolution (#20945; Refuted)
escape_witness: none
Direct frozen dependencies: none.

Per-declaration proof_shape:
* empty_unshifted_eq: bind-only; consumers: first_coefficient_eq.
* first_coefficient_eq: bind-only; consumers: half_parameter_family_neg.
* half_parameter_family_neg: bind-only; consumers: result.
* half_parameter_cond13: bind-only; consumers: result.
* result: bind-only; external conjecture settlement #20945.
Each row has escape_witness: none. These classifications use unfolding,
Mathlib instantiation and normalization; no escape-witness basis is asserted.
Direct D5 reuse: Defs.coeff, Defs.turanCoeff, Defs.esymm and Defs.cond13.
TwoBlockDefs supplies the same-delivery definitions and claim.
The decisive Mathlib facts are Real.Gamma_nat_eq_factorial,
Real.Gamma_nat_add_half, Real.pi_lt_d2, pow_le_pow_left₀,
pow_le_pow_right₀ and Finset.esymm_map_val.
The module certifies a parameter instance refuting TwoBlockDefs.claim, so
the utility kind is certified-instance with basis refutes.
-/

import D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockDefs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open scoped BigOperators
open D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockDefs

namespace D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult

private lemma empty_unshifted_eq {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ)
    (μ α β : ℝ) (m : ℕ) :
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) a b μ α β m =
      Defs.turanCoeff a b μ α β m := by
  unfold twoBlockTuranCoeff Defs.turanCoeff
  apply Finset.sum_congr rfl
  intro k hk
  simp only [seriesCoeff, pochRatio, Fin.prod_univ_zero, div_one, one_mul]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div]

private lemma first_coefficient_eq (q : ℕ) :
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 =
      (45 * Real.pi / 16) * (1 / 2 : ℝ) ^ q -
        4 * (16 / (9 * Real.pi)) ^ q - 6 * (16 / (15 * Real.pi)) ^ q := by
  rw [empty_unshifted_eq]
  have hc (t : ℝ) :
      Defs.coeff (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ)) t =
        Real.Gamma (1 + t) * (Real.Gamma (1 / 2 + t))⁻¹ ^ q := by
    simp [Defs.coeff, div_eq_mul_inv, inv_pow]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have g2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have g3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have g4 : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
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
  have gleading : 2 * (Real.Gamma (5 / 2) * Real.Gamma (7 / 2)) =
      45 * Real.pi / 16 := by
    rw [g52, g72]
    nlinarith [hsq]
  have expand :
      Defs.turanCoeff (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
        1 (1 / 2) (1 / 2) 1 =
        2 * (Real.Gamma (5 / 2) * Real.Gamma (7 / 2)) *
            ((Real.Gamma 2)⁻¹ ^ q * (Real.Gamma 3)⁻¹ ^ q) -
          (Real.Gamma 3) ^ 2 *
            ((Real.Gamma (5 / 2))⁻¹ ^ q * (Real.Gamma (5 / 2))⁻¹ ^ q) -
          Real.Gamma 2 * Real.Gamma 4 *
            ((Real.Gamma (3 / 2))⁻¹ ^ q * (Real.Gamma (7 / 2))⁻¹ ^ q) := by
    simp only [Defs.turanCoeff, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc,
      Nat.cast_zero, Nat.cast_one, Nat.sub_zero, Nat.sub_self, Nat.factorial_zero,
      Nat.factorial_one, mul_one, div_one, add_zero]
    norm_num <;> ring
  rw [expand, e1, e2, e3, gleading, g2, g3, g4]
  ring

/-- A one-entry shifted numerator and at least seven half denominator
parameters give a negative first coefficient at the unit base and half shifts. -/
theorem half_parameter_family_neg (q : ℕ) (hq : 7 ≤ q) :
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 < 0 := by
  have hbase : (640 / 567 : ℝ) < 32 / (9 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity : 0 < 9 * Real.pi)).2
    nlinarith [Real.pi_lt_d2]
  have hone : (1 : ℝ) ≤ 32 / (9 * Real.pi) := by linarith
  have hseven : 45 * Real.pi / 64 < (32 / (9 * Real.pi)) ^ 7 := by
    calc
      45 * Real.pi / 64 < 45 * (3.15 : ℝ) / 64 := by
        linarith [Real.pi_lt_d2]
      _ < (640 / 567 : ℝ) ^ 7 := by norm_num
      _ ≤ (32 / (9 * Real.pi)) ^ 7 :=
        pow_le_pow_left₀ (by norm_num) hbase.le 7
  have hpower : 45 * Real.pi / 64 < (32 / (9 * Real.pi)) ^ q :=
    hseven.trans_le (pow_le_pow_right₀ hone hq)
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

private lemma half_parameter_cond13 :
    Defs.cond13 (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 7 => (1 / 2 : ℝ)) := by
  have he (n k : ℕ) (x : ℝ) :
      Defs.esymm (fun _ : Fin n => x) k = (n.choose k : ℝ) * x ^ k := by
    rw [Defs.esymm, Finset.esymm_map_val]
    calc
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ _i ∈ t, x =
          ∑ _t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, x ^ k := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
      _ = (n.choose k : ℝ) * x ^ k := by simp
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  norm_num [he]

/-- The coefficient nonnegativity clause of Conjecture 2 is false. -/
theorem result : ¬ TwoBlockDefs.claim := by
  intro hclaim
  have hnonneg := hclaim 0 0 1 7
    (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 7 => (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; exact Fin.elim0 i) (by intro j; exact Fin.elim0 j)
    (by intro i; norm_num) (by intro j; norm_num)
    (by intro j hj; exact (Nat.not_lt_zero j hj).elim) half_parameter_cond13
    1 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) 1
  exact (not_lt_of_ge hnonneg) (half_parameter_family_neg 7 (by norm_num))

end D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
