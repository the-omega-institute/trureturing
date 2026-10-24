/- GID: D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim
   digest: A nonempty shifted numerator gives negative first coefficients for all q ≥ 7. -/

/-
# Negative first coefficients for the two-block hypergeometric Turanian

admission_basis: open-problem-resolution (#20945; Refuted)
escape_witness: none
Direct frozen dependencies: none.

Per-declaration proof_shape:
* pochRatio: bind-only definition; consumer: seriesCoeff.
* seriesCoeff: bind-only definition; consumers: twoBlockTuranCoeff, empty_unshifted_eq.
* twoBlockTuranCoeff: bind-only definition; consumers: claim, empty_unshifted_eq,
  first_coefficient_eq, half_parameter_family_neg.
* claim: bind-only definition; consumer: result.
* empty_unshifted_eq: bind-only; consumers: first_coefficient_eq.
* first_coefficient_eq: bind-only; consumers: half_parameter_family_neg,
  Reg.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.first_readout_pos.
* half_parameter_family_neg: bind-only; consumers: result.
* half_parameter_cond13: bind-only; consumers: result.
* result: bind-only; external conjecture settlement #20945.
Each row has escape_witness: none. These classifications use unfolding,
Mathlib instantiation and normalization; no escape-witness basis is asserted.
Direct D5 reuse: Defs.coeff, Defs.turanCoeff, Defs.esymm and Defs.cond13.
Shared bind-only helpers and their consumers:
* Defs.gamma_three_halves: Defs.gamma_three_seven_halves_inv_pow_mul.
* Defs.gamma_five_halves: Defs.gamma_five_halves_inv_pow_mul, first_coefficient_eq.
* Defs.gamma_seven_halves: Defs.gamma_three_seven_halves_inv_pow_mul, first_coefficient_eq.
* Defs.gamma_five_halves_inv_pow_mul: first_coefficient_eq, Result.first_coefficient_eq.
* Defs.gamma_three_seven_halves_inv_pow_mul: first_coefficient_eq,
  Result.first_coefficient_eq.
* Defs.pi_base_bound: half_parameter_family_neg, Result.half_parameter_family_neg.
All six shared helpers have proof_shape: bind-only and escape_witness: none.
The decisive Mathlib facts are Real.Gamma_two, Real.Gamma_nat_eq_factorial,
Real.pi_lt_d2, pow_le_pow_left₀,
pow_le_pow_right₀ and Finset.esymm_map_val.
The module certifies a parameter instance refuting TwoBlockResult.claim, so
the utility kind is certified-instance with basis refutes.
-/

import D5.S3.Analytic.HypergeometricShiftTuran.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult

/-- The ratio of rising factorial products for the unshifted parameter block. -/
def pochRatio {p₁ q₁ : ℕ} (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ) (n : ℕ) : ℝ :=
  (∏ i, (ascPochhammer ℝ n).eval (a₁ i)) /
    ∏ j, (ascPochhammer ℝ n).eval (b₁ j)

/-- The degree `n` Taylor coefficient in equation (3), including its factorial. -/
def seriesCoeff {p₁ q₁ p₂ q₂ : ℕ}
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  pochRatio a₁ b₁ n * Defs.coeff a₂ b₂ (μ + n) / (n.factorial : ℝ)

/-- The finite Cauchy coefficient of the generalized Turanian for two blocks. -/
def twoBlockTuranCoeff {p₁ q₁ p₂ q₂ : ℕ}
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (seriesCoeff a₁ b₁ a₂ b₂ (μ + α) k *
        seriesCoeff a₁ b₁ a₂ b₂ (μ + β) (m - k) -
      seriesCoeff a₁ b₁ a₂ b₂ μ k *
        seriesCoeff a₁ b₁ a₂ b₂ (μ + α + β) (m - k))

/-- The coefficient clause of Conjecture 2, with a nonempty shifted numerator. -/
def claim : Prop :=
  ∀ (p₁ q₁ p₂ q₂ : ℕ)
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ),
    p₁ ≤ q₁ → 1 ≤ p₂ → p₂ ≤ q₂ →
      (∀ i, 0 < a₁ i) → (∀ j, 0 < b₁ j) →
      (∀ i, 0 < a₂ i) → (∀ j, 0 < b₂ j) →
      Defs.cond13 a₁ b₁ → Defs.cond13 a₂ b₂ →
      ∀ μ α β : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β →
        ∀ m : ℕ, 0 ≤ twoBlockTuranCoeff a₁ b₁ a₂ b₂ μ α β m

private lemma empty_unshifted_eq {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ)
    (μ α β : ℝ) (m : ℕ) :
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) a b μ α β m =
      Defs.turanCoeff a b μ α β m := by
  unfold twoBlockTuranCoeff Defs.turanCoeff
  apply Finset.sum_congr rfl
  intro k hk
  simp only [seriesCoeff, pochRatio, Fin.prod_univ_zero, div_one, one_mul]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div]

lemma first_coefficient_eq (q : ℕ) :
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
  have e1 : (Real.Gamma 2)⁻¹ ^ q * (Real.Gamma 3)⁻¹ ^ q = (1 / 2 : ℝ) ^ q := by
    rw [Real.Gamma_two,
      show Real.Gamma (3 : ℝ) = 2 by
        rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
        norm_num [Nat.factorial],
      ← mul_pow]
    norm_num
  have gleading : 2 * (Real.Gamma (5 / 2) * Real.Gamma (7 / 2)) =
      45 * Real.pi / 16 := by
    rw [Defs.gamma_five_halves, Defs.gamma_seven_halves]
    nlinarith [Real.mul_self_sqrt Real.pi_pos.le]
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
  rw [expand, e1, Defs.gamma_five_halves_inv_pow_mul,
    Defs.gamma_three_seven_halves_inv_pow_mul, gleading, Real.Gamma_two,
    show Real.Gamma (3 : ℝ) = 2 by
      rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial],
    show Real.Gamma (4 : ℝ) = 6 by
      rw [show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]]
  ring

/-- A one-entry shifted numerator and at least seven half denominator
parameters give a negative first coefficient at the unit base and half shifts. -/
theorem half_parameter_family_neg (q : ℕ) (hq : 7 ≤ q) :
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 < 0 := by
  have hbase := Defs.pi_base_bound
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
theorem result : ¬ TwoBlockResult.claim := by
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
