/- GID: D5/S3/Analytic/EllipticTailExponent/Bounds
   generality: G
   mirror-B: D5/B/S3/Analytic/EllipticTailExponent/Bounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.PSeries, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Positive normalized elliptic coefficients and summably bounded negative derivatives. -/

import D5.S3.Analytic.EllipticTailExponent.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section
open Finset Set Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.EllipticTailExponent.Bounds

/-- The normalized coefficient for a positive tail index. -/
def b (k : ℕ) (a : ℝ) : ℝ :=
  (1 - a / k) / ((k : ℝ) * (k + 1)) *
    ∏ j ∈ range (k - 1), (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)

private def P (m : ℕ) (a : ℝ) : ℝ :=
  ∏ j ∈ range m, (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)

private lemma factor_bounds (j : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    0 < 1 - a ^ 2 / ((j : ℝ) + 1) ^ 2 ∧
      1 - a ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ 1 := by
  have hj : (1 : ℝ) ≤ j + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hj0 : 0 < (j : ℝ) + 1 := by positivity
  constructor
  · have : a ^ 2 < ((j : ℝ) + 1) ^ 2 := by nlinarith
    exact sub_pos.mpr ((div_lt_one (sq_pos_of_pos hj0)).2 this)
  · exact sub_le_self _ (by positivity)

private lemma P_bounds (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    0 < P m a ∧ P m a ≤ 1 := by
  exact ⟨Finset.prod_pos (fun j _ => (factor_bounds j ha ha1).1),
    Finset.prod_le_one₀ (fun j _ => (factor_bounds j ha ha1).1.le)
      (fun j _ => (factor_bounds j ha ha1).2)⟩

private lemma sum_inv_sq_le (m : ℕ) :
    (∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) ^ 2) ≤ 2 := by
  have h (m : ℕ) :
      (∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) ^ 2) ≤ 2 - 2 / ((m : ℝ) + 1) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ]
      push_cast
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hstep : (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤
          2 / ((m : ℝ) + 1) - 2 / ((m : ℝ) + 1 + 1) := by
        field_simp
        nlinarith
      linarith
  exact (h m).trans (sub_le_self _ (by positivity))

private lemma differentiable_P (m : ℕ) : Differentiable ℝ (P m) := by
  unfold P
  fun_prop

private lemma deriv_P_bounds (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    -(4 * a) ≤ deriv (P m) a ∧ deriv (P m) a ≤ 0 := by
  have hdiff (j : ℕ) :
      HasDerivAt (fun x : ℝ => 1 - x ^ 2 / ((j : ℝ) + 1) ^ 2)
        (-(2 * a / ((j : ℝ) + 1) ^ 2)) a := by
    convert (hasDerivAt_const a (1 : ℝ)).sub
      (((hasDerivAt_id a).pow 2).div_const (((j : ℝ) + 1) ^ 2)) using 1
    · ext x; dsimp
    · dsimp; ring
  have hd := HasDerivAt.fun_finsetProd (u := range m) (fun j _ => hdiff j)
  have he : deriv (P m) a = ∑ j ∈ range m,
      (∏ i ∈ (range m).erase j, (1 - a ^ 2 / ((i : ℝ) + 1) ^ 2)) *
        (-(2 * a / ((j : ℝ) + 1) ^ 2)) := by
    exact hd.deriv
  have hp (j : ℕ) :
      0 ≤ ∏ i ∈ (range m).erase j, (1 - a ^ 2 / ((i : ℝ) + 1) ^ 2) ∧
      (∏ i ∈ (range m).erase j, (1 - a ^ 2 / ((i : ℝ) + 1) ^ 2)) ≤ 1 :=
    ⟨Finset.prod_nonneg (fun i _ => (factor_bounds i ha ha1).1.le),
      Finset.prod_le_one₀ (fun i _ => (factor_bounds i ha ha1).1.le)
        (fun i _ => (factor_bounds i ha ha1).2)⟩
  rw [he]
  constructor
  · calc
      -(4 * a) ≤ -(2 * a * ∑ j ∈ range m, (1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left (sum_inv_sq_le m) (by positivity : 0 ≤ 2 * a)]
      _ = ∑ j ∈ range m, -(2 * a / ((j : ℝ) + 1) ^ 2) := by
        simp only [mul_sum, sum_neg_distrib, mul_one_div]
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        have hn : -(2 * a / ((j : ℝ) + 1) ^ 2) ≤ 0 := neg_nonpos.mpr (by positivity)
        nlinarith [(hp j).2]
  · apply sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (hp j).1 (neg_nonpos.mpr (by positivity))

/-- The normalized coefficients are positive and bounded by a summable rational sequence. -/
theorem b_bounds {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    0 < b k a ∧ b k a ≤ 1 / ((k : ℝ) * (k + 1)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlin : 0 < 1 - a / k := by
    exact sub_pos.mpr ((div_lt_one hk0).2 (by linarith))
  have hlin1 : 1 - a / k ≤ 1 := sub_le_self _ (div_nonneg ha hk0.le)
  change 0 < (1 - a / k) / ((k : ℝ) * (k + 1)) * P (k - 1) a ∧ _
  constructor
  · exact mul_pos (div_pos hlin (by positivity)) (P_bounds _ ha ha1).1
  · change (1 - a / k) / ((k : ℝ) * (k + 1)) * P (k - 1) a ≤ _
    calc
      _ ≤ (1 - a / k) / ((k : ℝ) * (k + 1)) :=
        mul_le_of_le_one_right (by positivity) (P_bounds _ ha ha1).2
      _ ≤ _ := div_le_div_of_nonneg_right hlin1 (by positivity)

/-- At parameter zero the normalized coefficient is the rational majorant. -/
theorem b_zero (k : ℕ) : b k 0 = 1 / ((k : ℝ) * (k + 1)) := by
  simp [b]

private lemma differentiable_b (k : ℕ) : Differentiable ℝ (b k) := by
  unfold b
  fun_prop

private lemma hasDerivAt_b (k : ℕ) (a : ℝ) :
    HasDerivAt (b k)
      ((-(1 / (k : ℝ)) * P (k - 1) a + (1 - a / k) * deriv (P (k - 1)) a) /
        ((k : ℝ) * (k + 1))) a := by
  have hl := ((hasDerivAt_const a (1 : ℝ)).sub ((hasDerivAt_id a).div_const (k : ℝ)))
  have hd := (hl.mul (differentiable_P (k - 1) a).hasDerivAt).div_const
    ((k : ℝ) * (k + 1))
  convert hd using 1
  · ext x
    dsimp [b, P]
    ring
  · dsimp; ring

/-- Each positive-index coefficient has a strictly negative, uniformly dominated derivative. -/
theorem deriv_b_bounds {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    deriv (b k) a < 0 ∧ |deriv (b k) a| ≤ 4 / ((k : ℝ) * (k + 1)) := by
  rw [(hasDerivAt_b k a).deriv]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hq : 0 < (k : ℝ) * (k + 1) := by positivity
  have hp := P_bounds (k - 1) ha ha1
  have hd := deriv_P_bounds (k - 1) ha ha1
  have hl : 0 < 1 - a / k := sub_pos.mpr ((div_lt_one hk0).2 (by linarith))
  have hl1 : 1 - a / k ≤ 1 := sub_le_self _ (div_nonneg ha hk0.le)
  have hneg : -(1 / (k : ℝ)) * P (k - 1) a +
      (1 - a / k) * deriv (P (k - 1)) a < 0 := by
    have := mul_neg_of_neg_of_pos (neg_neg_of_pos (one_div_pos.mpr hk0)) hp.1
    have := mul_nonpos_of_nonneg_of_nonpos hl.le hd.2
    linarith
  constructor
  · exact div_neg_of_neg_of_pos hneg hq
  · rw [abs_of_neg (div_neg_of_neg_of_pos hneg hq), ← neg_div]
    apply (div_le_div_iff_of_pos_right hq).2
    have hinv : (1 : ℝ) / k ≤ 1 := (div_le_one hk0).2 hk1
    have hm1 : (1 / (k : ℝ)) * P (k - 1) a ≤ 1 := by
      exact (mul_le_of_le_one_right (by positivity) hp.2).trans hinv
    have hm2 : -(4 * a) ≤ (1 - a / k) * deriv (P (k - 1)) a := by
      have h := mul_le_mul_of_nonpos_right hl1 hd.2
      nlinarith
    nlinarith

/-- The normalized positive tail. -/
def U (n : ℕ) (a : ℝ) : ℝ := ∑' k : ℕ, b (k + n + 1) a

private def w (n k : ℕ) : ℝ :=
  1 / (((k + n + 1 : ℕ) : ℝ) * (((k + n + 1 : ℕ) : ℝ) + 1))

private lemma summable_w (n : ℕ) : Summable (w n) := by
  have h := (summable_nat_add_iff (n + 1)).2
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply Summable.of_nonneg_of_le (fun k => by dsimp [w]; positivity) _ h
  intro k
  have hk : (0 : ℝ) < (k + n + 1 : ℕ) := by positivity
  dsimp [w]
  simpa only [Nat.add_assoc] using
    (one_div_le_one_div_of_le (sq_pos_of_pos hk)
      (show (((k + n + 1 : ℕ) : ℝ)) ^ 2 ≤
        ((k + n + 1 : ℕ) : ℝ) * (((k + n + 1 : ℕ) : ℝ) + 1) by nlinarith))

private lemma summable_b (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    Summable (fun k => b (k + n + 1) a) := by
  exact Summable.of_nonneg_of_le (fun k => (b_bounds (by omega) ha ha1).1.le)
    (fun k => (b_bounds (by omega) ha ha1).2) (summable_w n)

private lemma summable_deriv_b (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) :
    Summable (fun k => deriv (b (k + n + 1)) a) := by
  apply Summable.of_norm_bounded ((summable_w n).mul_left 4)
  intro k
  simpa only [Real.norm_eq_abs, w, mul_one_div] using
    (deriv_b_bounds (by omega : 1 ≤ k + n + 1) ha ha1).2

/-- Termwise differentiation on an open interval containing the right endpoint. -/
theorem hasDerivAt_U (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 3 / 4) :
    HasDerivAt (U n) (∑' k : ℕ, deriv (b (k + n + 1)) a) a := by
  apply hasDerivAt_tsum_of_isPreconnected
    (t := Ioo (0 : ℝ) (3 / 4)) (y₀ := (1 / 2 : ℝ))
    ((summable_w n).mul_left 4) isOpen_Ioo (convex_Ioo _ _).isPreconnected
  · intro k x hx
    exact (differentiable_b _ x).hasDerivAt
  · intro k x hx
    simpa only [Real.norm_eq_abs, w, mul_one_div] using
      (deriv_b_bounds (by omega : 1 ≤ k + n + 1) hx.1.le hx.2.le).2
  · norm_num
  · exact summable_b n (by norm_num) (by norm_num)
  · exact ⟨ha, ha1⟩

/-- The tail is positive, including at the limiting parameter zero. -/
theorem U_pos (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) : 0 < U n a := by
  exact (summable_b n ha ha1).tsum_pos
    (fun k => (b_bounds (by omega) ha ha1).1.le) 0
    (b_bounds (by omega) ha ha1).1

/-- The derivative of the tail is strictly negative. -/
theorem deriv_U_neg (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 3 / 4) :
    deriv (U n) a < 0 := by
  rw [(hasDerivAt_U n ha ha1).deriv]
  have h := (summable_deriv_b n ha.le ha1.le).tsum_lt_tsum
    (fun k => (deriv_b_bounds (by omega : 1 ≤ k + n + 1) ha.le ha1.le).1.le)
    ((deriv_b_bounds (by omega : 1 ≤ 0 + n + 1) ha.le ha1.le).1) summable_zero
  simpa only [tsum_zero] using h

/-- The positive tail has a continuous extension to parameter zero. -/
theorem continuousOn_U (n : ℕ) : ContinuousOn (U n) (Icc 0 (3 / 4)) := by
  apply continuousOn_tsum
    (fun k => (differentiable_b (k + n + 1)).continuous.continuousOn) (summable_w n)
  intro k a ha
  rw [Real.norm_eq_abs, abs_of_pos (b_bounds (by omega) ha.1 ha.2).1]
  exact (b_bounds (by omega) ha.1 ha.2).2

/-- The exact value of the normalized tail at zero. -/
theorem U_zero (n : ℕ) : U n 0 = 1 / ((n : ℝ) + 1) := by
  have hsum (N : ℕ) : ∑ k ∈ range N, w n k =
      1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + n + 1) := by
    have ht := sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + n + 1)) N
    convert ht using 1
    apply sum_congr rfl
    intro k hk
    dsimp [w]
    push_cast
    have h0 : (k : ℝ) + n + 1 ≠ 0 := by positivity
    have h1 : (k : ℝ) + n + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
    all_goals simp
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ range N, w n k) atTop
      (𝓝 (1 / ((n : ℝ) + 1))) := by
    simp_rw [hsum]
    have hz : Tendsto (fun N : ℕ => (1 : ℝ) / (((N + n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat n)
    have hz' : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + n + 1)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add] using hz
    simpa using tendsto_const_nhds.sub hz'
  have ht := tendsto_nhds_unique (summable_w n).hasSum.tendsto_sum_nat hlim
  simpa only [U, b_zero, w] using ht

/-- A parameter-independent summable bound for the tail derivative. -/
theorem norm_deriv_U_le (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 3 / 4) :
    ‖deriv (U n) a‖ ≤ 4 * ∑' k : ℕ,
      1 / (((k + n + 1 : ℕ) : ℝ) * (((k + n + 1 : ℕ) : ℝ) + 1)) := by
  rw [(hasDerivAt_U n ha ha1).deriv]
  calc
    _ ≤ ∑' k : ℕ, ‖deriv (b (k + n + 1)) a‖ := norm_tsum_le_tsum_norm
      (summable_deriv_b n ha.le ha1.le).norm
    _ ≤ ∑' k : ℕ, 4 * w n k := by
      exact Summable.tsum_le_tsum
        (fun k => by simpa only [Real.norm_eq_abs, w, mul_one_div] using
          (deriv_b_bounds (by omega : 1 ≤ k + n + 1) ha.le ha1.le).2)
        (summable_deriv_b n ha.le ha1.le).norm ((summable_w n).mul_left 4)
    _ = _ := tsum_mul_left

end D5.S3.Analytic.EllipticTailExponent.Bounds
