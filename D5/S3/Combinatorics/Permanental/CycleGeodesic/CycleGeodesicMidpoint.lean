/- GID: D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint
   mirror-E: none(waiver:direct-Lean-proof)
   anchors: []
   utility: none
   digest: The midpoint expansion has an explicit quadratic remainder. -/

/- Mathematical classification:
   product_even_zero: proof_shape: bind-only; escape_witness: none; consumer: midpoint_even_of_product
   odd_prod_double_factorial: proof_shape: bind-only; escape_witness: none; consumer: product_odd_exact
   product_odd_exact: proof_shape: bind-only; escape_witness: none; consumer: product_odd_amplitude
   midpoint_even_of_product: proof_shape: bind-only; escape_witness: none; consumer: result2
   stirlingError_tendsto: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_upper, stirlingError_lower
   reciprocal_step: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_upper, stirlingError_lower, stirlingError_remainder
   stirling_step_lower: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_lower
   tendsto_stirling_upper_envelope: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_upper, stirlingError_lower
   stirlingError_upper: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_remainder
   stirlingError_lower: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_remainder
   stirlingError_remainder: proof_shape: bind-only; escape_witness: none; consumer: stirlingError_remainder_index
   stirlingError_formula: proof_shape: bind-only; escape_witness: none; consumer: log_midpointRatio
   odd_double_factorial_factorial: proof_shape: bind-only; escape_witness: none; consumer: midpointAmplitude_eq_double_factorial
   midpointAmplitude_eq_double_factorial: proof_shape: bind-only; escape_witness: none; consumer: product_odd_amplitude
   midpointAmplitude_pos: proof_shape: bind-only; escape_witness: none; consumer: midpoint_log_norm_product, midpoint_rate_of_product, midpointRatio_pos
   midpointRatio_pos: proof_shape: bind-only; escape_witness: none; consumer: midpointRatio_eq_exp
   product_odd_amplitude: proof_shape: bind-only; escape_witness: none; consumer: midpoint_log_norm_product, midpoint_ratio_of_product
   midpoint_ratio_of_product: proof_shape: bind-only; escape_witness: none; consumer: result2
   log_midpointRatio: proof_shape: bind-only; escape_witness: none; consumer: midpoint_rate_of_product, midpointRatio_eq_exp
   log_mesh_error: proof_shape: bind-only; escape_witness: none; consumer: midpoint_log_error
   stirlingError_remainder_index: proof_shape: bind-only; escape_witness: none; consumer: midpoint_log_error
   midpoint_log_error: proof_shape: bind-only; escape_witness: none; consumer: midpointLogRatio_abs_le, midpointRatio_second_order_positive
   midpointRatio_eq_exp: proof_shape: bind-only; escape_witness: none; consumer: midpointRatio_second_order_positive
   midpointLogRatio_abs_le: proof_shape: bind-only; escape_witness: none; consumer: midpointLogRatio_tendsto, midpointRatio_second_order_positive
   midpointRatio_second_order_positive: proof_shape: bind-only; escape_witness: none; consumer: midpointRatio_second_order
   midpointRatio_second_order: proof_shape: bind-only; escape_witness: none; consumer: result2
   result2: proof_shape: content; escape_witness: CycleGeodesic.gaudin_permanent; consumer: none
   escape_witness: CycleGeodesic.gaudin_permanent: ∀ n : ℕ, ∀ x y : Fin n → ℂ, Function.Injective x → (∀ i j, x i ≠ y j) → (gaudin x y).det = (cauchy x y).permanent
   admission_basis: open-problem-resolution (#13612; Proved)
   Direct frozen dependencies: none at the immutable origin/dev baseline.
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicProduct
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped BigOperators Topology
open Filter Finset Polynomial Matrix Equiv Real
namespace CycleGeodesic

def midpointScale (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ ((n - 1) / 2) * 2 * (Real.exp (-(n : ℝ)) : ℂ)

private lemma product_even_zero {n : ℕ} (hn : 1 ≤ n) (he : Even n) : productValue n (-1) = 0 := by
  obtain ⟨m, rfl⟩ := he
  unfold productValue
  have hm : 0 < m := by omega
  have hfin : m < m + m := by omega
  have hp : (∏ k : Fin (m + m), (((m + m : ℕ) : ℂ) - k + (k : ℂ) * (-1))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨m, hfin⟩ : Fin (m + m)))
    push_cast
    ring
  rw [hp, mul_zero]

private lemma odd_prod_double_factorial (m : ℕ) :
    (∏ k ∈ range m, (2 * (k : ℂ) + 1)) = ((2 * m - 1).doubleFactorial : ℂ) := by
  cases m with
  | zero => simp [Nat.doubleFactorial]
  | succ m =>
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, prod_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_add, mul_one, Nat.cast_add, Nat.cast_one]
    have h := congrArg (fun k : ℕ => (k : ℂ)) (Nat.doubleFactorial_eq_prod_odd m)
    simpa only [Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h.symm

private lemma product_odd_exact (m : ℕ) : productValue (2 * m + 1) (-1) =
    (-1 : ℂ) ^ m * ((2 * m + 1).doubleFactorial : ℂ) *
      ((2 * m - 1).doubleFactorial : ℂ) / (2 * m + 1 : ℂ) ^ (2 * m + 1) := by
  unfold productValue
  rw [show (∏ k : Fin (2 * m + 1), (((2 * m + 1 : ℕ) : ℂ) - k + (k : ℂ) * (-1))) =
    ∏ k ∈ range (2 * m + 1), (((2 * m + 1 : ℕ) : ℂ) - k + (k : ℂ) * (-1)) from
      Fin.prod_univ_eq_prod_range (fun k => (((2 * m + 1 : ℕ) : ℂ) - k + (k : ℂ) * (-1))) _]
  have hfun : (fun k : ℕ => ((2 * m + 1 : ℕ) : ℂ) - k + (k : ℂ) * (-1)) =
    (fun k : ℕ => (2 * m + 1 : ℂ) - 2 * k) := by ext k; push_cast; ring
  rw [hfun, show 2 * m + 1 = (m + 1) + m by omega, prod_range_add]
  have hpos : (∏ k ∈ range (m + 1), ((2 * m + 1 : ℂ) - 2 * k)) =
      ((2 * m + 1).doubleFactorial : ℂ) := by
    rw [← prod_range_reflect]
    have hr : (∏ k ∈ range (m + 1), ((2 * m + 1 : ℂ) - 2 * ((m + 1 - 1 - k : ℕ) : ℂ))) =
        ∏ k ∈ range (m + 1), (2 * (k : ℂ) + 1) := by
      apply prod_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      rw [show m + 1 - 1 - k = m - k by omega, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hr, odd_prod_double_factorial]
    congr 2
  have hneg : (∏ k ∈ range m, ((2 * m + 1 : ℂ) - 2 * (m + 1 + k : ℕ))) =
      (-1 : ℂ) ^ m * ((2 * m - 1).doubleFactorial : ℂ) := by
    have hr : (∏ k ∈ range m, ((2 * m + 1 : ℂ) - 2 * (m + 1 + k : ℕ))) =
        ∏ k ∈ range m, ((-1 : ℂ) * (2 * k + 1)) := by
      apply prod_congr rfl
      intro k hk
      push_cast
      ring
    rw [hr, prod_mul_distrib, prod_const, card_range, odd_prod_double_factorial]
  rw [hpos, hneg]
  push_cast
  rw [inv_pow, ← div_eq_inv_mul]
  ring

lemma midpoint_even_of_product (hp : ProductFormula) {n : ℕ}
    (hn : 1 ≤ n) (he : Even n) : (gamma n (1 / 2)).permanent = 0 := by
  rw [hp n hn (1 / 2) (by norm_num) (by norm_num), q_midpoint]
  exact product_even_zero hn he

def stirlingError (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)

private lemma stirlingError_tendsto : Tendsto stirlingError atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)) atTop (𝓝 0)
  have h := ((Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const (Real.log (Real.sqrt Real.pi))
  simpa [stirlingError] using h

private lemma reciprocal_step {x : ℝ} (hx : 0 < x) :
    1 / (12 * x) - 1 / (12 * (x + 1)) = 1 / (12 * x * (x + 1)) := by
  field_simp
  ring

private lemma stirling_step_lower (n : ℕ) :
    1 / (12 * ((n : ℝ) + 2) * ((n : ℝ) + 3)) ≤
      Real.log (Stirling.stirlingSeq (n + 1)) -
        Real.log (Stirling.stirlingSeq (n + 2)) := by
  have hs := Stirling.log_stirlingSeq_sdiff_hasSum n
  have h0 := sum_le_hasSum ({0} : Finset ℕ) (fun j _ => by positivity) hs
  simp only [Finset.sum_singleton, Nat.cast_one, Nat.cast_add, pow_one] at h0
  have hlead : 1 / (12 * ((n : ℝ) + 2) * ((n : ℝ) + 3)) ≤
      1 / (2 * (1 : ℝ) + 1) * ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have heq : (1 / (2 * (1 : ℝ) + 1) * ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2)) =
        1 / (3 * (2 * ((n : ℝ) + 1) + 1) ^ 2) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  refine hlead.trans ?_
  simpa only [Nat.cast_zero, zero_add, zero_add, pow_one] using h0

private lemma tendsto_stirling_upper_envelope :
    Tendsto (fun n : ℕ => (1 : ℝ) / (12 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).div_const 12
  convert! h using 1
  · ext n
    rw [div_div]
    congr 1
    ring
  · norm_num

private lemma stirlingError_upper (n : ℕ) : stirlingError (n + 1) ≤ 1 / (12 * ((n : ℝ) + 1)) := by
  have hm : Monotone (fun k : ℕ =>
      stirlingError (k + 1) - 1 / (12 * ((k : ℝ) + 1))) := by
    apply monotone_nat_of_le_succ
    intro k
    have h := Stirling.log_stirlingSeq_sdiff_le (k + 1)
    have hr := reciprocal_step (x := (k : ℝ) + 1) (by positivity)
    simp only [stirlingError, Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at *
    have heq : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [heq] at hr h ⊢
    linarith
  have ht := (stirlingError_tendsto.comp (tendsto_add_atTop_nat 1)).sub
    tendsto_stirling_upper_envelope
  have h := hm.ge_of_tendsto ht n
  simpa only [sub_self, sub_nonpos] using h

private lemma stirlingError_lower (n : ℕ) : 1 / (12 * ((n : ℝ) + 2)) ≤ stirlingError (n + 1) := by
  have hm : Antitone (fun k : ℕ =>
      stirlingError (k + 1) - 1 / (12 * ((k : ℝ) + 2))) := by
    apply antitone_nat_of_succ_le
    intro k
    have h := stirling_step_lower k
    have hr := reciprocal_step (x := (k : ℝ) + 2) (by positivity)
    simp only [stirlingError, Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at *
    have heq : (k : ℝ) + 2 + 1 = (k : ℝ) + 3 := by ring
    have heq' : (k : ℝ) + 1 + 2 = (k : ℝ) + 3 := by ring
    rw [heq] at hr
    rw [heq']
    linarith
  have hg : Tendsto (fun k : ℕ => (1 : ℝ) / (12 * ((k : ℝ) + 2))) atTop (𝓝 0) := by
    have h := tendsto_stirling_upper_envelope.comp (tendsto_add_atTop_nat 1)
    convert! h using 1
    ext k
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  have ht := (stirlingError_tendsto.comp (tendsto_add_atTop_nat 1)).sub hg
  have h := hm.le_of_tendsto ht n
  simpa only [sub_self, sub_nonneg] using h

private lemma stirlingError_remainder (n : ℕ) :
    |stirlingError (n + 1) - 1 / (12 * ((n : ℝ) + 1))| ≤
      1 / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [abs_le]
  have hu := stirlingError_upper n
  have hl := stirlingError_lower n
  have hr := reciprocal_step (x := (n : ℝ) + 1) (by positivity)
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hr
  constructor <;> linarith [show 0 ≤ 1 / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) by positivity]

private lemma stirlingError_formula {n : ℕ} (hn : n ≠ 0) :
    stirlingError n = Real.log (n.factorial : ℝ) -
      ((n : ℝ) + 1 / 2) * Real.log n + n - (1 / 2) * Real.log (2 * Real.pi) := by
  unfold stirlingError
  rw [Stirling.log_stirlingSeq_formula]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hn),
    Real.log_div (by exact_mod_cast hn) (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_sqrt Real.pi_pos.le,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

def midpointAmplitude (m : ℕ) : ℝ :=
  (((2 * m + 1).factorial : ℝ) ^ 2) /
    (2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 * (2 * m + 1 : ℝ) ^ (2 * m + 2))

def midpointRatio (m : ℕ) : ℝ := midpointAmplitude m / (2 * Real.exp (-(2 * m + 1 : ℝ)))

def midpointLogRatio (m : ℕ) : ℝ :=
  (2 * m + 1 : ℝ) * (-Real.log (1 - 1 / (2 * m + 1 : ℝ))) - 1 +
    2 * stirlingError (2 * m + 1) - 2 * stirlingError m

private lemma odd_double_factorial_factorial (m : ℕ) :
    ((2 * m + 1).doubleFactorial : ℝ) * (2 ^ m * (m.factorial : ℝ)) =
      ((2 * m + 1).factorial : ℝ) := by
  have h := Nat.factorial_eq_mul_doubleFactorial (2 * m)
  rw [Nat.doubleFactorial_two_mul] at h
  exact_mod_cast h.symm

private lemma midpointAmplitude_eq_double_factorial (m : ℕ) :
    midpointAmplitude m = ((2 * m + 1).doubleFactorial : ℝ) *
      ((2 * m - 1).doubleFactorial : ℝ) / (2 * m + 1 : ℝ) ^ (2 * m + 1) := by
  have h := odd_double_factorial_factorial m
  have hdf : ((2 * m + 1).doubleFactorial : ℝ) =
      (2 * m + 1 : ℝ) * ((2 * m - 1).doubleFactorial : ℝ) := by
    rw [Nat.doubleFactorial_add_one]
    push_cast
    rfl
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  unfold midpointAmplitude
  rw [← h, hdf]
  simp only [mul_pow, ← pow_mul, Nat.mul_comm m 2]
  field_simp
  ring

lemma midpointAmplitude_pos (m : ℕ) : 0 < midpointAmplitude m := by
  unfold midpointAmplitude
  positivity

private lemma midpointRatio_pos (m : ℕ) : 0 < midpointRatio m := by
  unfold midpointRatio
  exact div_pos (midpointAmplitude_pos m) (by positivity)

lemma product_odd_amplitude (m : ℕ) :
    productValue (2 * m + 1) (-1) = (-1 : ℂ) ^ m * (midpointAmplitude m : ℂ) := by
  rw [product_odd_exact, midpointAmplitude_eq_double_factorial]
  push_cast
  ring

lemma midpoint_ratio_of_product (hp : ProductFormula) (m : ℕ) :
    (gamma (2 * m + 1) (1 / 2)).permanent / midpointScale (2 * m + 1) =
      (midpointRatio m : ℂ) := by
  rw [hp _ (by omega) _ (by norm_num) (by norm_num), q_midpoint, product_odd_amplitude]
  unfold midpointScale midpointRatio
  rw [show (2 * m + 1 - 1) / 2 = m by omega]
  push_cast
  field_simp

lemma log_midpointRatio {m : ℕ} (hm : m ≠ 0) :
    Real.log (midpointRatio m) = midpointLogRatio m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  have hnR : (0 : ℝ) < 2 * m + 1 := by positivity
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hnfac : (0 : ℝ) < (2 * m + 1).factorial := by positivity
  have hl : Real.log (1 - 1 / (2 * m + 1 : ℝ)) =
      Real.log 2 + Real.log m - Real.log (2 * m + 1 : ℝ) := by
    rw [show 1 - 1 / (2 * m + 1 : ℝ) = (2 * m) / (2 * m + 1) by field_simp; ring,
      Real.log_div (by positivity) hnR.ne', Real.log_mul (by norm_num) hmR.ne']
  unfold midpointRatio midpointAmplitude midpointLogRatio
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_exp,
    stirlingError_formula (by omega : 2 * m + 1 ≠ 0), stirlingError_formula hm, hl]
  push_cast
  ring

private lemma log_mesh_error {n : ℝ} (hn : 3 ≤ n) :
    |n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n)| ≤ 2 / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hx0 : 0 < 1 / n := by positivity
  have hx1 : 1 / n < 1 := (div_lt_one hn0).2 (by linarith)
  have ht := Real.abs_log_sub_add_sum_range_le (x := 1 / n)
    (by rw [abs_of_pos hx0]; exact hx1) 2
  norm_num [Finset.sum_range_succ] at ht
  have ht' : |1 / n + (1 / n) ^ 2 / 2 + Real.log (1 - 1 / n)| ≤
      (1 / n) ^ 3 / (1 - 1 / n) := by
    simpa [abs_of_pos hn0, div_pow] using ht
  have heq : n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n) =
      -n * (1 / n + (1 / n) ^ 2 / 2 + Real.log (1 - 1 / n)) := by
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_pos hn0]
  calc
    _ ≤ n * ((1 / n) ^ 3 / (1 - 1 / n)) := mul_le_mul_of_nonneg_left ht' hn0.le
    _ = 1 / (n * (n - 1)) := by field_simp <;> ring
    _ ≤ 2 / n ^ 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < n * (n - 1)) (by positivity : 0 < n ^ 2)).2
      nlinarith

private lemma stirlingError_remainder_index {n : ℕ} (hn : n ≠ 0) :
    |stirlingError n - 1 / (12 * (n : ℝ))| ≤ 1 / (12 * (n : ℝ) * ((n : ℝ) + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [Nat.cast_add, Nat.cast_one, Nat.add_comm, Nat.succ_eq_add_one, add_assoc, one_add_one_eq_two] using stirlingError_remainder k

private lemma midpoint_log_error (m : ℕ) (hm : 1 ≤ m) :
    |(2 * m + 1 : ℝ) * (-Real.log (1 - 1 / (2 * m + 1 : ℝ))) - 1 +
        2 * stirlingError (2 * m + 1) - 2 * stirlingError m - 1 / (3 * (2 * m + 1 : ℝ))| ≤
      5 / (2 * m + 1 : ℝ) ^ 2 := by
  let n : ℝ := 2 * m + 1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : 3 ≤ n := by dsimp [n]; linarith
  have hn0 : 0 < n := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have en := stirlingError_remainder_index (by omega : 2 * m + 1 ≠ 0)
  have em := stirlingError_remainder_index (by omega : m ≠ 0)
  have hncast : ((2 * m + 1 : ℕ) : ℝ) = n := by simp [n]
  rw [hncast] at en
  have hlog := log_mesh_error hn
  have hrat : |1 / (3 * n) - 1 / (6 * (m : ℝ))| ≤ 1 / n ^ 2 := by
    have heq : 1 / (3 * n) - 1 / (6 * (m : ℝ)) = -1 / (6 * n * m) := by
      dsimp [n]
      field_simp
      ring
    rw [heq, abs_div, abs_neg, abs_one, abs_of_pos (by positivity : 0 < 6 * n * m)]
    apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < n ^ 2)).2
    dsimp [n]
    nlinarith
  have hen : 2 * (1 / (12 * n * (n + 1))) ≤ 1 / n ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < n ^ 2)).2
    nlinarith
  have hem : 2 * (1 / (12 * (m : ℝ) * ((m : ℝ) + 1))) ≤ 1 / n ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < n ^ 2)).2
    dsimp [n]
    nlinarith
  change |n * (-Real.log (1 - 1 / n)) - 1 + 2 * stirlingError (2 * m + 1) -
    2 * stirlingError m - 1 / (3 * n)| ≤ 5 / n ^ 2
  have heq : n * (-Real.log (1 - 1 / n)) - 1 + 2 * stirlingError (2 * m + 1) -
      2 * stirlingError m - 1 / (3 * n) =
    (n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n)) +
      2 * (stirlingError (2 * m + 1) - 1 / (12 * n)) -
      2 * (stirlingError m - 1 / (12 * (m : ℝ))) + (1 / (3 * n) - 1 / (6 * (m : ℝ))) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n)| +
        |2 * (stirlingError (2 * m + 1) - 1 / (12 * n))| +
        |2 * (stirlingError m - 1 / (12 * (m : ℝ)))| + |1 / (3 * n) - 1 / (6 * (m : ℝ))| := by
      have h1 := abs_add_le (n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n))
        (2 * (stirlingError (2 * m + 1) - 1 / (12 * n)))
      have h2 := abs_sub
        ((n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n)) +
          2 * (stirlingError (2 * m + 1) - 1 / (12 * n)))
        (2 * (stirlingError m - 1 / (12 * (m : ℝ))))
      have h3 := abs_add_le
        ((n * (-Real.log (1 - 1 / n)) - 1 - 1 / (2 * n)) +
          2 * (stirlingError (2 * m + 1) - 1 / (12 * n)) -
          2 * (stirlingError m - 1 / (12 * (m : ℝ))))
        (1 / (3 * n) - 1 / (6 * (m : ℝ)))
      linarith
    _ ≤ 2 / n ^ 2 + 1 / n ^ 2 + 1 / n ^ 2 + 1 / n ^ 2 := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (add_le_add (add_le_add hlog
        ((mul_le_mul_of_nonneg_left en (by norm_num)).trans hen))
        ((mul_le_mul_of_nonneg_left em (by norm_num)).trans hem)) hrat
    _ = 5 / n ^ 2 := by ring

private lemma midpointRatio_eq_exp {m : ℕ} (hm : m ≠ 0) :
    midpointRatio m = Real.exp (midpointLogRatio m) := by
  rw [← log_midpointRatio hm, Real.exp_log (midpointRatio_pos m)]

lemma midpointLogRatio_abs_le {m : ℕ} (hm : 1 ≤ m) :
    |midpointLogRatio m| ≤ 2 / (2 * m + 1 : ℝ) := by
  let n : ℝ := 2 * m + 1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : 3 ≤ n := by dsimp [n]; linarith
  have hn0 : 0 < n := by linarith
  have h := midpoint_log_error m hm
  change |midpointLogRatio m - 1 / (3 * n)| ≤ 5 / n ^ 2 at h
  have hcomb : 5 / n ^ 2 + 1 / (3 * n) ≤ 2 / n := by
    apply (le_div_iff₀ hn0).2
    rw [show (5 / n ^ 2 + 1 / (3 * n)) * n = 5 / n + 1 / 3 by field_simp <;> ring]
    have h5 : 5 / n ≤ 5 / 3 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
    linarith
  have ht := abs_add_le (midpointLogRatio m - 1 / (3 * n)) (1 / (3 * n))
  rw [sub_add_cancel, abs_of_pos (by positivity : 0 < 1 / (3 * n))] at ht
  change |midpointLogRatio m| ≤ 2 / n
  linarith

private lemma midpointRatio_second_order_positive {m : ℕ} (hm : 1 ≤ m) :
    |midpointRatio m - 1 - 1 / (3 * (2 * m + 1 : ℝ))| ≤ 9 / (2 * m + 1 : ℝ) ^ 2 := by
  let n : ℝ := 2 * m + 1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : 3 ≤ n := by dsimp [n]; linarith
  have hn0 : 0 < n := by linarith
  have ha := midpointLogRatio_abs_le hm
  have hb : |midpointLogRatio m| ≤ 1 := ha.trans ((div_le_one hn0).2 (by linarith))
  have he := Real.abs_exp_sub_one_sub_id_le hb
  have hsq : (midpointLogRatio m) ^ 2 ≤ 4 / n ^ 2 := by
    calc
      _ = |midpointLogRatio m| ^ 2 := (sq_abs _).symm
      _ ≤ (2 / n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ = 4 / n ^ 2 := by ring
  have hl := midpoint_log_error m hm
  change |midpointLogRatio m - 1 / (3 * n)| ≤ 5 / n ^ 2 at hl
  rw [midpointRatio_eq_exp (by omega : m ≠ 0)]
  change |Real.exp (midpointLogRatio m) - 1 - 1 / (3 * n)| ≤ 9 / n ^ 2
  rw [show Real.exp (midpointLogRatio m) - 1 - 1 / (3 * n) =
    (Real.exp (midpointLogRatio m) - 1 - midpointLogRatio m) +
      (midpointLogRatio m - 1 / (3 * n)) by ring]
  apply (abs_add_le _ _).trans
  have h := add_le_add (he.trans hsq) hl
  rw [show 4 / n ^ 2 + 5 / n ^ 2 = 9 / n ^ 2 by ring] at h
  exact h

lemma midpointRatio_second_order (m : ℕ) :
    |midpointRatio m - 1 - 1 / (3 * (2 * m + 1 : ℝ))| ≤ 16 / (2 * m + 1 : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · subst m
    have hR : midpointRatio 0 = Real.exp 1 / 2 := by
      simp [midpointRatio, midpointAmplitude, Real.exp_neg, div_eq_mul_inv]
    rw [hR]
    norm_num
    rw [abs_le]
    constructor <;> linarith [Real.exp_one_lt_three, Real.exp_pos 1]
  · have h := midpointRatio_second_order_positive (m := m) (by omega)
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))

#print axioms midpoint_even_of_product
#print axioms midpointAmplitude_pos
#print axioms product_odd_amplitude
#print axioms midpoint_ratio_of_product
#print axioms log_midpointRatio
#print axioms midpointLogRatio_abs_le
#print axioms midpointRatio_second_order
def claim2 : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → Odd n →
    ‖(gamma n (1 / 2)).permanent / midpointScale n - 1 - (1 / (3 * (n : ℂ)))‖ ≤
      C / (n : ℝ) ^ 2) ∧
  (∀ n : ℕ, 1 ≤ n → Even n → (gamma n (1 / 2)).permanent = 0)

theorem result2 : claim2 := by
  constructor
  · refine ⟨16, by norm_num, ?_⟩
    intro n hn ho
    obtain ⟨m, rfl⟩ := ho
    rw [midpoint_ratio_of_product product_formula]
    have heq : (midpointRatio m : ℂ) - 1 - 1 / (3 * (2 * m + 1 : ℂ)) =
        ((midpointRatio m - 1 - 1 / (3 * (2 * m + 1 : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    push_cast
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    simpa using midpointRatio_second_order m
  · intro n hn he
    exact midpoint_even_of_product product_formula hn he

#print axioms result2
end CycleGeodesic
