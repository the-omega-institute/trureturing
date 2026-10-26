/- GID: D5/S3/Analytic/HypergeometricShiftTuran/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral, mathlib/module/Mathlib.RingTheory.MvPolynomial.Symmetric.Defs]
   utility: none
   digest: Gamma ratios, shared special values, and shifted Turanian coefficients. -/

/-
# Shared Gamma ratios and special values

Escape audit unfinished for the public helpers: https://github.com/the-omega-institute/trureturing/issues/20966

Per-declaration proof_shape:
* coeff: bind-only definition; consumers: turanCoeff, TwoBlockResult.seriesCoeff.
* turanCoeff: bind-only definition; consumers: claim, Result.first_coefficient_eq,
  TwoBlockResult.empty_unshifted_eq.
* esymm: bind-only definition; consumers: cond13, esymm_const.
* esymm_const: bind-only; consumers: TwoBlockResult.half_parameter_cond13,
  FunctionResult.witness_cond13.
  Direct frozen dependency: D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm;
    statement_id=sha256:4d8858460f0aad49d26a6547cf056cdd7fa4c7ed94938e4abfb0b427d2150a59.
* cond13: bind-only definition; consumers: claim, TwoBlockResult.claim,
  TwoBlockResult.half_parameter_cond13.
* claim: bind-only definition; consumer: Result.result.
* gamma_three_halves: bind-only; consumer: gamma_three_seven_halves_inv_pow_mul.
* gamma_five_halves: bind-only; consumers: gamma_five_halves_inv_pow_mul,
  TwoBlockResult.first_coefficient_eq.
* gamma_seven_halves: bind-only; consumers: gamma_three_seven_halves_inv_pow_mul,
  TwoBlockResult.first_coefficient_eq.
* gamma_five_halves_inv_pow_mul: bind-only; consumers: Result.first_coefficient_eq,
  TwoBlockResult.first_coefficient_eq.
* gamma_three_seven_halves_inv_pow_mul: bind-only;
  consumers: Result.first_coefficient_eq, TwoBlockResult.first_coefficient_eq.
* gamma_three: bind-only; consumers: gamma_two_three_inv_pow_mul,
  TwoBlockResult.first_coefficient_eq.
* gamma_two_three_inv_pow_mul: bind-only; consumers: Result.first_coefficient_eq,
  TwoBlockResult.first_coefficient_eq.
* base_pow_mul_half_pow: bind-only; consumers: Result.half_parameter_family_neg,
  TwoBlockResult.half_parameter_family_neg.
* pi_base_bound: bind-only; consumers: Result.half_parameter_family_neg,
  TwoBlockResult.half_parameter_family_neg.
Each row has escape_witness: none. Except for esymm_const as listed above,
Direct frozen dependencies: none.
This is the shared supporting dependency of the coefficient and function Result modules;
its consumed helpers supply neither an escape witness nor a separate admission basis.
The utility is none: these definitions and general identities are supporting
objects, not a bounded enumeration, checker, numeric reduction or certified instance.
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.HypergeometricShiftTuran.Defs

/-- The Gamma product ratio, with empty parameter products equal to one. -/
def coeff {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (t : ℝ) : ℝ :=
  (∏ i, Real.Gamma (a i + t)) / ∏ j, Real.Gamma (b j + t)

/-- The coefficient of degree `m` in the shifted Turanian, including factorial weights. -/
def turanCoeff {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ)
    (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (coeff a b (μ + α + k) * coeff a b (μ + β + ((m - k : ℕ) : ℝ)) -
      coeff a b (μ + k) * coeff a b (μ + α + β + ((m - k : ℕ) : ℝ))) /
      ((k.factorial : ℝ) * ((m - k).factorial : ℝ))

/-- The elementary symmetric function of the entries, retaining multiplicities. -/
def esymm {p : ℕ} (a : Fin p → ℝ) (k : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin p)).val.map a).esymm k

/-- The elementary symmetric function of a constant vector. -/
lemma esymm_const (n k : ℕ) (x : ℝ) :
    esymm (fun _ : Fin n => x) k = (n.choose k : ℝ) * x ^ k := by
  rw [esymm, Finset.esymm_map_val]
  calc
    ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ _i ∈ t, x =
        ∑ _t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, x ^ k := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    _ = (n.choose k : ℝ) * x ^ k := by simp

/-- Consecutive inequalities in the elementary symmetric ratio chain. -/
def cond13 {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) : Prop :=
  ∀ j : ℕ, j < p →
    esymm b (q - j) / esymm a (p - j) ≤
      esymm b (q - j - 1) / esymm a (p - j - 1)

/-- The coefficient assertion for the branch with no more numerator parameters
than denominator parameters. -/
def claim : Prop :=
  ∀ (p q : ℕ) (a : Fin p → ℝ) (b : Fin q → ℝ),
    p ≤ q → (∀ i, 0 < a i) → (∀ j, 0 < b j) → cond13 a b →
      ∀ μ α β : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β → α ≤ β + 1 →
        ∀ m : ℕ, 0 ≤ turanCoeff a b μ α β m

/-- The Gamma value at three halves. -/
lemma gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
  norm_num [Nat.doubleFactorial]

/-- The Gamma value at five halves. -/
lemma gamma_five_halves : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
  rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
  norm_num [Nat.doubleFactorial]

/-- The Gamma value at seven halves. -/
lemma gamma_seven_halves : Real.Gamma (7 / 2) = 15 * Real.sqrt Real.pi / 8 := by
  rw [show (7 / 2 : ℝ) = ((3 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
  norm_num [Nat.doubleFactorial]

/-- The balanced reciprocal Gamma power product. -/
lemma gamma_five_halves_inv_pow_mul (q : ℕ) :
    (Real.Gamma (5 / 2))⁻¹ ^ q * (Real.Gamma (5 / 2))⁻¹ ^ q =
      (16 / (9 * Real.pi)) ^ q := by
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  rw [← mul_pow, gamma_five_halves]
  congr 1
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  nlinarith [hsq]

/-- The outer reciprocal Gamma power product. -/
lemma gamma_three_seven_halves_inv_pow_mul (q : ℕ) :
    (Real.Gamma (3 / 2))⁻¹ ^ q * (Real.Gamma (7 / 2))⁻¹ ^ q =
      (16 / (15 * Real.pi)) ^ q := by
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  rw [← mul_pow, gamma_three_halves, gamma_seven_halves]
  congr 1
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  nlinarith [hsq]

/-- A rational lower bound for the exponential comparison base. -/
lemma pi_base_bound : (640 / 567 : ℝ) < 32 / (9 * Real.pi) := by
  apply (lt_div_iff₀ (by positivity : 0 < 9 * Real.pi)).2
  nlinarith [Real.pi_lt_d2]

/-- The Gamma value at three. -/
lemma gamma_three : Real.Gamma 3 = 2 := by
  rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

/-- The integer reciprocal Gamma power product. -/
lemma gamma_two_three_inv_pow_mul (q : ℕ) :
    (Real.Gamma 2)⁻¹ ^ q * (Real.Gamma 3)⁻¹ ^ q = (1 / 2 : ℝ) ^ q := by
  rw [Real.Gamma_two, gamma_three, ← mul_pow]
  norm_num

/-- The comparison base times one half is the balanced base. -/
lemma base_pow_mul_half_pow (q : ℕ) :
    (32 / (9 * Real.pi)) ^ q * (1 / 2 : ℝ) ^ q = (16 / (9 * Real.pi)) ^ q := by
  rw [← mul_pow]
  congr 1
  ring

end D5.S3.Analytic.HypergeometricShiftTuran.Defs
