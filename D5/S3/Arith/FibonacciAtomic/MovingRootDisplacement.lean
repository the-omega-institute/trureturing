/- GID: D5/S3/Arith/FibonacciAtomic/MovingRootDisplacement
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/MovingRootDisplacement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite-product errors and additive Fibonacci density root displacement. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement

open scoped BigOperators Topology
open Filter Set SourceDensityMonotonicity

/-- Cassini correction to the first moment. -/
noncomputable def kappa (k : ℕ) : ℝ := 1 / ((L k : ℝ) * A k * D k)

/-- Bounded part of the additive displacement. -/
noncomputable def sigma (k : ℕ) : ℝ :=
  (D k : ℝ) / L k + (E k : ℝ) / (2 * A k) + (A k : ℝ) / (2 * D k)

/-- First moment of the three normalized finite-product blocks. -/
noncomputable def B (k j : ℕ) : ℝ := sigma k + kappa k * ((j : ℝ) + 1 / 2)

private theorem log_error (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hp : 0 < 1 + x := by have := (abs_le.mp hx).1; linarith
  have hc := Complex.norm_log_one_add_sub_self_le (z := (x : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans_lt (by norm_num))
  have he : Complex.log (1 + (x : ℂ)) - (x : ℂ) =
      ((Real.log (1 + x) - x : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_log hp.le]
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hc
  have hi : (1 - |x|)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ (by linarith : 0 < 1 - |x|) (by norm_num)).mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg x)]

private theorem fib_data (k : ℕ) (hk : 1 ≤ k) :
    0 < E k ∧ 0 < A k ∧ 0 < D k ∧ 0 < L k ∧
    E k ≤ A k ∧ D k = E k + A k ∧ L k = A k + D k := by
  refine ⟨Nat.fib_pos.mpr (by omega), Nat.fib_pos.mpr (by omega),
    Nat.fib_pos.mpr (by omega), Nat.fib_pos.mpr (by omega),
    Nat.fib_mono (by omega), ?_, ?_⟩
  · simpa only [D, E, A, show 3 * k - 2 + 1 = 3 * k - 1 by omega,
      show 3 * k - 2 + 2 = 3 * k by omega, add_comm] using
      (Nat.fib_add_two (n := 3 * k - 2))
  · simpa only [L, A, D, show 3 * k - 1 + 1 = 3 * k by omega,
      show 3 * k - 1 + 2 = 3 * k + 1 by omega, add_comm] using
      (Nat.fib_add_two (n := 3 * k - 1))

private theorem sum_indices (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * (m - 1) / 2 := by
  rcases m with _ | m
  · simp
  · have h := congrArg (fun z : ℕ => (z : ℝ)) (Finset.sum_range_id_mul_two (m + 1))
    push_cast at h ⊢
    linarith

private theorem block_log (m : ℕ) (s u t J : ℝ) (hs : 0 < s)
    (hJ : 0 < J) (ht : 2 * J ≤ t)
    (hb : ∀ i ∈ Finset.range m, |(u + i) / s| ≤ J) :
    |Real.log (rising (s * t + u) m) -
      (m : ℝ) * Real.log (s * t) -
      ((m : ℝ) * u + m * (m - 1) / 2) / (s * t)| ≤
      (m : ℝ) * J ^ 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hx (i : ℕ) (hi : i ∈ Finset.range m) :
      |(u + i) / (s * t)| ≤ 1 / 2 := by
    rw [← div_div, abs_div, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr (by linarith [hb i hi])
  have hp (i : ℕ) (hi : i ∈ Finset.range m) : 0 < s * t + u + i := by
    have h := (abs_le.mp (hx i hi)).1
    have he : s * t + u + i = s * t * (1 + (u + i) / (s * t)) := by
      field_simp; ring
    rw [he]
    exact mul_pos (mul_pos hs ht0) (by linarith)
  have hlog : Real.log (rising (s * t + u) m) =
      (m : ℝ) * Real.log (s * t) +
        ∑ i ∈ Finset.range m, Real.log (1 + (u + i) / (s * t)) := by
    rw [rising, Real.log_prod (fun i hi => (hp i hi).ne')]
    simp_rw [show ∀ i : ℕ, s * t + u + i = s * t * (1 + (u + i) / (s * t)) by
      intro i; field_simp; ring]
    rw [Finset.sum_congr rfl (fun i hi => Real.log_mul (mul_pos hs ht0).ne'
      (by have := (abs_le.mp (hx i hi)).1; linarith)), Finset.sum_add_distrib]
    simp
  have hsum : (∑ i ∈ Finset.range m, (u + (i : ℝ)) / (s * t)) =
      ((m : ℝ) * u + m * (m - 1) / 2) / (s * t) := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, sum_indices]
    simp
  rw [hlog, add_sub_cancel_left, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range m, |Real.log (1 + (u + i) / (s * t)) -
        (u + i) / (s * t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, J ^ 2 / t ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      refine (log_error _ (hx i hi)).trans ?_
      rw [← div_div, div_pow]
      exact div_le_div_of_nonneg_right (sq_le_sq.mpr (by simpa [abs_of_pos hJ] using hb i hi))
        (sq_nonneg t)
    _ = _ := by simp; ring

set_option maxHeartbeats 2000000 in
-- Simultaneous normalization expands the three blocks and the Cassini polynomial.
/-- Exact coefficient and quadratic error for every legal large real argument. -/
theorem quantitative_expansion (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (t : ℝ)
    (ht : 2 * ((j : ℝ) + 1) ≤ t) :
    |Real.log (H k j t / c k) - B k j / t| ≤
      2 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / t ^ 2 := by
  obtain ⟨heN, haN, hdN, hlN, heaN, hdaN, hldN⟩ := fib_data k hk
  have he : (0 : ℝ) < E k := by exact_mod_cast heN
  have ha : (0 : ℝ) < A k := by exact_mod_cast haN
  have hd : (0 : ℝ) < D k := by exact_mod_cast hdN
  have hl : (0 : ℝ) < L k := by exact_mod_cast hlN
  have hea : (E k : ℝ) ≤ A k := by exact_mod_cast heaN
  have hda : (D k : ℝ) = E k + A k := by exact_mod_cast hdaN
  have hld : (L k : ℝ) = A k + D k := by exact_mod_cast hldN
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ht0 : 0 < t := by linarith
  have he1 : (1 : ℝ) ≤ E k := by exact_mod_cast heN
  have hα (i : ℕ) (hi : i ∈ Finset.range (E k)) :
      |((E k : ℝ) * j + 1 + i) / A k| ≤ (j : ℝ) + 1 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ ha]
    have hi' : (i : ℝ) + 1 ≤ E k := by exact_mod_cast Finset.mem_range.mp hi
    nlinarith [mul_le_mul_of_nonneg_right hea hj]
  have hβ (i : ℕ) (hi : i ∈ Finset.range (A k)) :
      |((A k : ℝ) * j + 1 + i) / D k| ≤ (j : ℝ) + 1 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hd]
    have hi' : (i : ℝ) + 1 ≤ A k := by exact_mod_cast Finset.mem_range.mp hi
    nlinarith [mul_nonneg he.le hj]
  have hγ (i : ℕ) (hi : i ∈ Finset.range (D k)) :
      |((D k : ℝ) * j - 1 / 2 + i) / L k| ≤ (j : ℝ) + 1 := by
    rw [abs_le, le_div_iff₀ hl, div_le_iff₀ hl]
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi' : (i : ℝ) < D k := by exact_mod_cast Finset.mem_range.mp hi
    constructor <;> nlinarith [mul_nonneg hd.le hj, mul_nonneg ha.le hj]
  have h₁ := block_log (E k) (A k) ((E k : ℝ) * j + 1) t ((j : ℝ) + 1)
    ha (by positivity) ht hα
  have h₂ := block_log (A k) (D k) ((A k : ℝ) * j + 1) t ((j : ℝ) + 1)
    hd (by positivity) ht hβ
  have h₃ := block_log (D k) (L k) ((D k : ℝ) * j - 1 / 2) t ((j : ℝ) + 1)
    hl (by positivity) ht hγ
  have hcass : ((A k : ℝ) ^ 2 - D k * E k) ^ 2 = 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ))
      (D5.S1.Scale.fib_cassini_from_golden_norm (3 * k - 2))
    push_cast at h
    rw [show 3 * k - 2 + 2 = 3 * k by omega,
      show 3 * k - 2 + 1 = 3 * k - 1 by omega] at h
    have hh := congrArg (fun z : ℝ => z ^ 2) h
    rw [← pow_mul, mul_comm (3 * k - 1) 2, pow_mul, neg_one_sq, one_pow] at hh
    dsimp [A, D, E]
    nlinarith only [hh]
  have hmoment :
      (((E k : ℝ) * ((E k : ℝ) * j + 1) + E k * (E k - 1) / 2) / A k +
        ((A k : ℝ) * ((A k : ℝ) * j + 1) + A k * (A k - 1) / 2) / D k -
        ((D k : ℝ) * ((D k : ℝ) * j - 1 / 2) + D k * (D k - 1) / 2) / L k) = B k j := by
    dsimp [B, sigma, kappa]
    field_simp
    rw [hld, hda] at *
    linear_combination (2 * (j : ℝ) + 1) * hcass
  have hrpos (s u : ℝ) (m : ℕ) (hs : 0 < s)
      (hb : ∀ i ∈ Finset.range m, |(u + i) / s| ≤ (j : ℝ) + 1) :
      0 < rising (s * t + u) m := by
    apply Finset.prod_pos
    intro i hi
    have hb' := (abs_le.mp (hb i hi)).1
    have := (le_div_iff₀ hs).mp hb'
    nlinarith [mul_pos hs ht0]
  have hp₁ := hrpos (A k) ((E k : ℝ) * j + 1) (E k) ha hα
  have hp₂ := hrpos (D k) ((A k : ℝ) * j + 1) (A k) hd hβ
  have hp₃ := hrpos (L k) ((D k : ℝ) * j - 1 / 2) (D k) hl hγ
  have hid : Real.log (H k j t / c k) =
      (Real.log (rising ((A k : ℝ) * t + ((E k : ℝ) * j + 1)) (E k)) -
        (E k : ℝ) * Real.log ((A k : ℝ) * t)) +
      (Real.log (rising ((D k : ℝ) * t + ((A k : ℝ) * j + 1)) (A k)) -
        (A k : ℝ) * Real.log ((D k : ℝ) * t)) -
      (Real.log (rising ((L k : ℝ) * t + ((D k : ℝ) * j - 1 / 2)) (D k)) -
        (D k : ℝ) * Real.log ((L k : ℝ) * t)) := by
    have hp₁' : rising (a k j t + 1) (E k) ≠ 0 := by simpa [a, add_assoc] using hp₁.ne'
    have hp₂' : rising (b k j t + 1) (A k) ≠ 0 := by simpa [b, add_assoc] using hp₂.ne'
    have hp₃' : rising (n k j t - 1 / 2) (D k) ≠ 0 := by
      simpa [n, sub_eq_add_neg, add_assoc] using hp₃.ne'
    rw [Real.log_div (by
      dsimp [H]
      exact div_ne_zero (mul_ne_zero hp₁' hp₂') (mul_ne_zero (by positivity) hp₃'))
      (by dsimp [c]; positivity)]
    dsimp only [H, c]
    rw [Real.log_div (mul_ne_zero hp₁' hp₂') (mul_ne_zero (by positivity) hp₃'),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul hp₁' hp₂', Real.log_mul (by positivity) hp₃',
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow, Real.log_mul ha.ne' ht0.ne',
      Real.log_mul hd.ne' ht0.ne', Real.log_mul hl.ne' ht0.ne']
    simp only [a, b, n, sub_eq_add_neg, add_assoc]
    rw [hda]
    ring
  have herr := (abs_sub_le
    ((Real.log (rising ((A k : ℝ) * t + ((E k : ℝ) * j + 1)) (E k)) -
      E k * Real.log ((A k : ℝ) * t) -
      ((E k : ℝ) * ((E k : ℝ) * j + 1) + E k * (E k - 1) / 2) / (A k * t)) +
    (Real.log (rising ((D k : ℝ) * t + ((A k : ℝ) * j + 1)) (A k)) -
      A k * Real.log ((D k : ℝ) * t) -
      ((A k : ℝ) * ((A k : ℝ) * j + 1) + A k * (A k - 1) / 2) / (D k * t)))
    0
    (Real.log (rising ((L k : ℝ) * t + ((D k : ℝ) * j - 1 / 2)) (D k)) -
      D k * Real.log ((L k : ℝ) * t) -
      ((D k : ℝ) * ((D k : ℝ) * j - 1 / 2) + D k * (D k - 1) / 2) / (L k * t)))
  simp only [sub_zero, zero_sub, abs_neg] at herr
  have herr' := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  have heq : Real.log (H k j t / c k) - B k j / t =
      (Real.log (rising ((A k : ℝ) * t + ((E k : ℝ) * j + 1)) (E k)) -
      E k * Real.log ((A k : ℝ) * t) -
      ((E k : ℝ) * ((E k : ℝ) * j + 1) + E k * (E k - 1) / 2) / (A k * t)) +
      (Real.log (rising ((D k : ℝ) * t + ((A k : ℝ) * j + 1)) (A k)) -
      A k * Real.log ((D k : ℝ) * t) -
      ((A k : ℝ) * ((A k : ℝ) * j + 1) + A k * (A k - 1) / 2) / (D k * t)) -
      (Real.log (rising ((L k : ℝ) * t + ((D k : ℝ) * j - 1 / 2)) (D k)) -
      D k * Real.log ((L k : ℝ) * t) -
      ((D k : ℝ) * ((D k : ℝ) * j - 1 / 2) + D k * (D k - 1) / 2) / (L k * t)) := by
    rw [hid, ← hmoment]
    ring
  rw [heq]
  calc
    _ ≤ _ := herr.trans (add_le_add herr' h₃)
    _ = _ := by rw [hda]; ring

private theorem coefficient_bounds (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    0 < c k ∧ c k ≤ (1 / 4 : ℝ) ^ D k ∧ 0 ≤ B k j ∧ B k j ≤ (j : ℝ) + 3 := by
  obtain ⟨heN, haN, hdN, hlN, heaN, hdaN, hldN⟩ := fib_data k hk
  have he : (1 : ℝ) ≤ E k := by exact_mod_cast heN
  have ha : (1 : ℝ) ≤ A k := by exact_mod_cast haN
  have hd : (1 : ℝ) ≤ D k := by exact_mod_cast hdN
  have hl : (1 : ℝ) ≤ L k := by exact_mod_cast hlN
  have hea : (E k : ℝ) ≤ A k := by exact_mod_cast heaN
  have hda : (D k : ℝ) = E k + A k := by exact_mod_cast hdaN
  have hld : (L k : ℝ) = A k + D k := by exact_mod_cast hldN
  have hc := (SourceDensityCrossing.result k hk j).1
  have hnum : (A k : ℝ) ^ E k * (D k : ℝ) ^ A k ≤ (L k : ℝ) ^ D k := by
    conv_rhs => rw [hdaN, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
  have hcp : c k ≤ (1 / 4 : ℝ) ^ D k := by
    dsimp [c]
    rw [one_div_pow]
    apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ D k * (L k : ℝ) ^ D k)).mpr
    simpa [field] using hnum
  have hkappa : kappa k ≤ 1 := by
    dsimp [kappa]
    apply (div_le_one (by positivity : 0 < (L k : ℝ) * A k * D k)).mpr
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hl ha) hd
  have hsigma : sigma k ≤ 2 := by
    have h₁ : (D k : ℝ) / L k ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have h₂ : (E k : ℝ) / (2 * A k) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A k)).mpr
      linarith
    have h₃ : (A k : ℝ) / (2 * D k) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D k)).mpr
      linarith
    dsimp [sigma]
    linarith
  refine ⟨hc, hcp, ?_, ?_⟩
  · dsimp [B, sigma, kappa]; positivity
  · dsimp [B]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [mul_le_mul_of_nonneg_right hkappa (show 0 ≤ (j : ℝ) + 1 / 2 by positivity)]

private theorem coefficient_decay :
    Tendsto (fun k : ℕ => (D k : ℝ) * c k) atTop (𝓝 0) ∧
    Tendsto c atTop (𝓝 0) := by
  have hD : Tendsto D atTop atTop := by
    apply tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨2, ?_⟩) tendsto_id
    intro k hk
    exact (show k ≤ 3 * k by omega).trans (Nat.le_fib_self (by omega))
  have hg := (tendsto_self_mul_const_pow_of_lt_one (r := (1 / 4 : ℝ))
    (by norm_num) (by norm_num)).comp hD
  have hc : Tendsto (fun k : ℕ => (D k : ℝ) * c k) atTop (𝓝 0) := by
    apply squeeze_zero' (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
      (eventually_atTop.2 ⟨1, fun k hk => ?_⟩) hg
    · exact mul_nonneg (Nat.cast_nonneg _) (coefficient_bounds k hk 0).1.le
    · exact mul_le_mul_of_nonneg_left (coefficient_bounds k hk 0).2.1 (Nat.cast_nonneg _)
  refine ⟨hc, ?_⟩
  apply squeeze_zero' (eventually_atTop.2 ⟨1, fun k hk => (coefficient_bounds k hk 0).1.le⟩)
    (eventually_atTop.2 ⟨1, fun k hk => ?_⟩) hc
  have hd : (1 : ℝ) ≤ D k := by exact_mod_cast (fib_data k hk).2.2.1
  exact le_mul_of_one_le_left (coefficient_bounds k hk 0).1.le hd

private theorem moving_log_control (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (s : ℝ)
    (hs : |s| ≤ 1)
    (hlarge : 4 * ((j : ℝ) + ((j : ℝ) + 3) + 1) ≤ ((j : ℝ) + 1) / c k) :
    let M := ((j : ℝ) + 1) / c k
    let b := (j : ℝ) + 3
    let t := M + j - B k j + s
    2 * ((j : ℝ) + 1) ≤ t ∧
    |Real.log (q k j t) - s / M| ≤
      ((b + 1) ^ 2 + 2 * b * (j + b + 1) + 8 * ((j : ℝ) + 1) ^ 2) *
        (D k : ℝ) / M ^ 2 := by
  dsimp only
  let M := ((j : ℝ) + 1) / c k
  let b := (j : ℝ) + 3
  let t := M + j - B k j + s
  change 2 * ((j : ℝ) + 1) ≤ t ∧ _
  obtain ⟨hc, _, hB0, hBb⟩ := coefficient_bounds k hk j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hJ : 0 < (j : ℝ) + 1 := by positivity
  have hM : 0 < M := div_pos hJ hc
  have hD : (1 : ℝ) ≤ D k := by exact_mod_cast (fib_data k hk).2.2.1
  have hs' := abs_le.mp hs
  have htM : M / 2 ≤ t := by dsimp [t, M, b] at *; linarith
  have htJ : 2 * ((j : ℝ) + 1) ≤ t := by dsimp [t, M, b] at *; linarith
  have ht0 : 0 < t := by linarith
  have htj : 0 < t - j := by linarith
  have hxb : |s - B k j| ≤ b + 1 := by
    apply abs_le.mpr
    constructor <;> dsimp [b] at * <;> linarith
  have hx : |(s - B k j) / M| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
    dsimp [M, b] at *
    linarith
  have herr₁ : |Real.log (1 + (s - B k j) / M) - (s - B k j) / M| ≤
      (b + 1) ^ 2 / M ^ 2 := by
    refine (log_error _ hx).trans ?_
    rw [div_pow]
    exact div_le_div_of_nonneg_right
      (sq_le_sq.mpr (by simpa [abs_of_nonneg (by positivity : 0 ≤ b + 1)] using hxb))
      (sq_nonneg M)
  have herr₂ : |Real.log (H k j t / c k) - B k j / t| ≤
      8 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / M ^ 2 := by
    refine (quantitative_expansion k hk j t htJ).trans ?_
    calc
      _ ≤ 2 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / (M / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (sq_le_sq₀ (by positivity) ht0.le |>.mpr htM)
      _ = _ := by field_simp <;> ring
  have hdiff : |M - t| ≤ (j : ℝ) + b + 1 := by
    apply abs_le.mpr
    dsimp [t, b] at *
    constructor <;> linarith
  have herr₃ : |B k j / t - B k j / M| ≤ 2 * b * (j + b + 1) / M ^ 2 := by
    have heq : B k j / t - B k j / M = B k j * (M - t) / (t * M) := by
      field_simp
    rw [heq, abs_div, abs_mul, abs_of_nonneg hB0, abs_of_pos (mul_pos ht0 hM)]
    calc
      _ ≤ b * (j + b + 1) / (t * M) := by
        gcongr
      _ ≤ b * (j + b + 1) / ((M / 2) * M) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right htM hM.le)
      _ = _ := by field_simp <;> ring
  have hq := ((SourceDensityCrossing.result k hk j).2.1 t (by linarith)).1
  have hH : 0 < H k j t := by
    have hmul : 0 < (t - j) * H k j t := (div_pos_iff_of_pos_right hJ).mp hq
    exact (mul_pos_iff_of_pos_left htj).mp hmul
  have heq : q k j t = (1 + (s - B k j) / M) * (H k j t / c k) := by
    dsimp [q, t, M]
    field_simp
    ring
  have hlog : Real.log (q k j t) = Real.log (1 + (s - B k j) / M) +
      Real.log (H k j t / c k) := by
    rw [heq, Real.log_mul (by have := (abs_le.mp hx).1; linarith) (div_pos hH hc).ne']
  refine ⟨htJ, ?_⟩
  change |Real.log (q k j t) - s / M| ≤ _
  have herr := (abs_add_le
    (Real.log (1 + (s - B k j) / M) - (s - B k j) / M)
    (Real.log (H k j t / c k) - B k j / t)).trans (add_le_add herr₁ herr₂)
  have hall := (abs_add_le
    ((Real.log (1 + (s - B k j) / M) - (s - B k j) / M) +
      (Real.log (H k j t / c k) - B k j / t))
    (B k j / t - B k j / M)).trans (add_le_add herr herr₃)
  have hid : Real.log (q k j t) - s / M =
      ((Real.log (1 + (s - B k j) / M) - (s - B k j) / M) +
      (Real.log (H k j t / c k) - B k j / t)) +
      (B k j / t - B k j / M) := by rw [hlog]; ring
  rw [hid]
  refine hall.trans ?_
  change _ ≤ ((b + 1) ^ 2 + 2 * b * (j + b + 1) + 8 * ((j : ℝ) + 1) ^ 2) *
    (D k : ℝ) / M ^ 2
  have hp : 0 ≤ (b + 1) ^ 2 + 2 * b * (j + b + 1) := by positivity
  have hmult := mul_le_mul_of_nonneg_left hD hp
  rw [← add_div, ← add_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hM)).mpr
  nlinarith only [hmult]

private theorem moving_crossings (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      let M := ((j : ℝ) + 1) / c k
      let tminus := M + j - B k j - C * D k * c k
      let tplus := M + j - B k j + C * D k * c k
      2 * ((j : ℝ) + 1) ≤ tminus ∧ q k j tminus < 1 ∧ 1 < q k j tplus := by
  let b := (j : ℝ) + 3
  let R := (b + 1) ^ 2 + 2 * b * (j + b + 1) + 8 * ((j : ℝ) + 1) ^ 2
  let C := (R + 1) / ((j : ℝ) + 1)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hJ : 0 < (j : ℝ) + 1 := by positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hthreshold : 0 < ((j : ℝ) + 1) / (4 * (j + b + 1)) := by positivity
  have htail : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧
      (D k : ℝ) * c k < 1 / C ∧ c k < ((j : ℝ) + 1) / (4 * (j + b + 1)) := by
    filter_upwards [eventually_ge_atTop 1,
      coefficient_decay.1.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / C)),
      coefficient_decay.2.eventually (eventually_lt_nhds hthreshold)] with k hk h₁ h₂
    exact ⟨hk, h₁, h₂⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp htail
  refine ⟨C, hC, max K 1, le_max_right _ _, ?_⟩
  intro k hk
  obtain ⟨hk1, hsmall, hlarge⟩ := hK k ((le_max_left K 1).trans hk)
  have hc := (coefficient_bounds k hk1 j).1
  have hd : (0 : ℝ) < D k := by exact_mod_cast (fib_data k hk1).2.2.1
  let M := ((j : ℝ) + 1) / c k
  let s := C * D k * c k
  have hM : 0 < M := div_pos hJ hc
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    have := (lt_div_iff₀ hC).mp hsmall
    dsimp [s]; nlinarith only [this]
  have hMlarge : 4 * ((j : ℝ) + ((j : ℝ) + 3) + 1) ≤ ((j : ℝ) + 1) / c k := by
    apply (le_div_iff₀ hc).mpr
    have := (lt_div_iff₀ (show 0 < 4 * (j + b + 1) by positivity)).mp hlarge
    dsimp [b] at this
    linarith
  have hm := moving_log_control k hk1 j (-s) (by simpa [abs_of_pos hs0] using hs1) hMlarge
  have hp := moving_log_control k hk1 j s (by simpa [abs_of_pos hs0] using hs1) hMlarge
  change 2 * ((j : ℝ) + 1) ≤ M + j - B k j + -s ∧
    |Real.log (q k j (M + j - B k j + -s)) - -s / M| ≤ R * D k / M ^ 2 at hm
  change 2 * ((j : ℝ) + 1) ≤ M + j - B k j + s ∧
    |Real.log (q k j (M + j - B k j + s)) - s / M| ≤ R * D k / M ^ 2 at hp
  have hmargin : R * (D k : ℝ) / M ^ 2 < s / M := by
    have heq : s / M = (R + 1) * (D k : ℝ) / M ^ 2 := by
      dsimp [s, C, M]
      field_simp
    rw [heq]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hM)).mpr (by nlinarith)
  have hlogm : Real.log (q k j (M + j - B k j - s)) < 0 := by
    have := (abs_le.mp hm.2).2
    simp only [neg_div, sub_neg_eq_add, ← sub_eq_add_neg] at this
    linarith
  have hlogp : 0 < Real.log (q k j (M + j - B k j + s)) := by
    have := (abs_le.mp hp.2).1
    linarith
  have hdomm : (j : ℝ) + 1 ≤ M + j - B k j - s := by
    have := hm.1
    linarith
  have hdomp : (j : ℝ) + 1 ≤ M + j - B k j + s := by linarith [hp.1]
  have hqm := ((SourceDensityCrossing.result k hk1 j).2.1 _ hdomm).1
  have hqp := ((SourceDensityCrossing.result k hk1 j).2.1 _ hdomp).1
  refine ⟨by simpa only [sub_eq_add_neg] using hm.1, ?_, ?_⟩
  · exact (Real.log_lt_log_iff hqm zero_lt_one).mp (by simpa using hlogm)
  · exact (Real.log_lt_log_iff zero_lt_one hqp).mp (by simpa using hlogp)

/-- For each fixed minority index, one tail and one constant control the root displacement.
The final clause is the exact logarithmic root equation on that same tail. -/
theorem root_displacement (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∃ τ : ℝ, (j : ℝ) + 1 ≤ τ ∧ q k j τ = 1 ∧
        (∀ x : ℝ, (j : ℝ) + 1 ≤ x → q k j x = 1 → x = τ) ∧
        |τ - (((j : ℝ) + 1) / c k + j - B k j)| ≤ C * D k * c k ∧
        |Real.log ((τ - j) / (((j : ℝ) + 1) / c k)) + B k j / τ| ≤
          2 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / τ ^ 2 := by
  obtain ⟨C, hC, K, hK, hcross⟩ := moving_crossings j
  refine ⟨C, hC, K, hK, ?_⟩
  intro k hk
  have hk1 := hK.trans hk
  have hsource := SourceDensityCrossing.result k hk1 j
  have hc := hsource.1
  have hmono := hsource.2.2.1
  obtain ⟨τ, ⟨hτ, hroot⟩, huniq⟩ := hsource.2.2.2.2.1
  obtain ⟨hminus, hqm, hqp⟩ := hcross k hk
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have herr0 : 0 < C * D k * c k := by
    have hd : (0 : ℝ) < D k := by exact_mod_cast (fib_data k hk1).2.2.1
    positivity
  have hdomm : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) / c k + j - B k j - C * D k * c k := by
    linarith
  have hdomp : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) / c k + j - B k j + C * D k * c k := by
    linarith
  have hlo : ((j : ℝ) + 1) / c k + j - B k j - C * D k * c k < τ :=
    (hmono.lt_iff_lt hdomm hτ).mp (by rwa [hroot])
  have hhi : τ < ((j : ℝ) + 1) / c k + j - B k j + C * D k * c k :=
    (hmono.lt_iff_lt hτ hdomp).mp (by rwa [hroot])
  have hτlarge : 2 * ((j : ℝ) + 1) ≤ τ := by linarith
  refine ⟨τ, hτ, hroot, fun x hx hr => huniq x ⟨hx, hr⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have htj : 0 < τ - j := by change (j : ℝ) + 1 ≤ τ at hτ; linarith
  have hH : H k j τ = ((j : ℝ) + 1) / (τ - j) := by
    dsimp [q] at hroot
    apply (eq_div_iff htj.ne').mpr
    have := (div_eq_one_iff_eq (by positivity : (j : ℝ) + 1 ≠ 0)).mp hroot
    nlinarith only [this]
  have hlog : Real.log (H k j τ / c k) =
      -Real.log ((τ - j) / (((j : ℝ) + 1) / c k)) := by
    rw [hH]
    have heq : (((j : ℝ) + 1) / (τ - j)) / c k =
        (((τ - j) / (((j : ℝ) + 1) / c k)))⁻¹ := by field_simp
    rw [heq, Real.log_inv]
  have h := quantitative_expansion k hk1 j τ hτlarge
  rw [hlog] at h
  simpa only [sub_eq_add_neg, ← neg_add, abs_neg] using h

end D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement

#print axioms D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement.quantitative_expansion
#print axioms D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement.root_displacement
