/- GID: D5/S3/Analytic/ExpRatioCM/Positive
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Positive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow, mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.ENNReal]
   utility: none
   digest: Nonnegative exponential coefficients imply complete monotonicity. -/

import D5.S3.Analytic.ExpRatioCM.Series
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Positive exponential coefficients and complete monotonicity. -/

open scoped BigOperators Topology
open Set
open D5.S3.Analytic.ExpRatioCM.Defs
open D5.S3.Analytic.ExpRatioCM.Series

namespace D5.S3.Analytic.ExpRatioCM.Positive

/-- Nonnegative exponential moments of all orders imply complete monotonicity. -/
theorem cm_of_nonnegative_exponential_expansion
    {h : ℝ → ℝ} {c r : ℕ → ℝ}
    (hsmooth : ContDiffOn ℝ ⊤ h (Ioi 0))
    (hderiv : ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k h t = (-1 : ℝ)^k *
        (∑' n : ℕ, c n * r n^k * Real.exp (-r n*t)))
    (hc : ∀ n, 0 ≤ c n) (hr : ∀ n, 0 ≤ r n) :
    CompletelyMonotoneOn h := by
  refine ⟨hsmooth, ?_⟩
  intro k t ht
  rw [hderiv k t ht]
  have hs : (-1:ℝ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, hs, one_mul]
  exact tsum_nonneg (fun n => mul_nonneg (mul_nonneg (hc n) (pow_nonneg (hr n) k))
    (Real.exp_pos _).le)

private lemma F_zero (t : ℝ) : F 0 t = 1 / (Real.exp t - 1) := by
  simp [F]

private lemma F_one {t : ℝ} (ht : 0 < t) :
    F 1 t = Real.exp t / (Real.exp t - 1)^2 := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have hd := (hasDerivAt_const t (1 : ℝ)).fun_div ((Real.hasDerivAt_exp t).sub_const 1) hn
  have hf := iteratedDeriv_F 0 1 t
  simp only [iteratedDeriv_one, pow_one, zero_add, neg_mul, one_mul] at hf
  have hbase : F 0 = (fun x : ℝ => 1 / (Real.exp x - 1)) := funext F_zero
  rw [hbase] at hf
  rw [hd.deriv] at hf
  simp only [zero_mul, one_mul, zero_sub, neg_div] at hf
  exact neg_injective hf.symm

private lemma F_two {t : ℝ} (ht : 0 < t) :
    F 2 t = Real.exp t * (Real.exp t + 1) / (Real.exp t - 1)^3 := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have he : F 1 =ᶠ[𝓝 t] (fun x : ℝ => Real.exp x / (Real.exp x - 1)^2) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact F_one hx
  have hd := (Real.hasDerivAt_exp t).fun_div
    (((Real.hasDerivAt_exp t).sub_const 1).fun_pow 2) (pow_ne_zero 2 hn)
  have hf := iteratedDeriv_F 1 1 t
  simp only [iteratedDeriv_one, pow_one, neg_mul, one_mul] at hf
  rw [he.deriv_eq, hd.deriv] at hf
  have hh : (Real.exp t * (Real.exp t - 1)^2 - Real.exp t *
      (2 * (Real.exp t - 1) * Real.exp t)) / ((Real.exp t - 1)^2)^2 =
      -(Real.exp t * (Real.exp t + 1) / (Real.exp t - 1)^3) := by
    field_simp; ring
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Nat.reduceAdd] at hf
  rw [hh] at hf
  linarith

private lemma F_three {t : ℝ} (ht : 0 < t) :
    F 3 t = Real.exp t * (Real.exp t^2 + 4*Real.exp t + 1) / (Real.exp t - 1)^4 := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have he : F 2 =ᶠ[𝓝 t] (fun x : ℝ => Real.exp x * (Real.exp x + 1) / (Real.exp x - 1)^3) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact F_two hx
  have hd := ((Real.hasDerivAt_exp t).fun_mul ((Real.hasDerivAt_exp t).add_const 1)).fun_div
    (((Real.hasDerivAt_exp t).sub_const 1).fun_pow 3) (pow_ne_zero 3 hn)
  have hf := iteratedDeriv_F 2 1 t
  simp only [iteratedDeriv_one, pow_one, neg_mul, one_mul] at hf
  rw [he.deriv_eq, hd.deriv] at hf
  have hh : ((Real.exp t * (Real.exp t + 1) + Real.exp t * Real.exp t) * (Real.exp t - 1)^3 -
      Real.exp t * (Real.exp t + 1) * (3 * (Real.exp t - 1)^2 * Real.exp t)) /
      ((Real.exp t - 1)^3)^2 =
      -(Real.exp t * (Real.exp t^2 + 4*Real.exp t + 1) / (Real.exp t - 1)^4) := by
    field_simp; ring
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Nat.reduceAdd] at hf
  rw [hh] at hf
  linarith

private lemma ratio_closed_forms {t : ℝ} (ht : 0 < t) :
    ratioF 0 t = 1 / (1 - Real.exp (-t)) ∧
    ratioF 1 t = (1 + Real.exp (-t)) / (1 - Real.exp (-t)) ∧
    ratioF 2 t = (1 + 4 * Real.exp (-t) + Real.exp (-t)^2) /
      (1 - Real.exp (-t)^2) ∧
    ratioG 0 t = Real.exp (-t) / (1 - Real.exp (-t)) := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have hp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hp1 : Real.exp t + 1 ≠ 0 := by positivity
  have he : Real.exp (2*t) = Real.exp t^2 := by rw [two_mul, Real.exp_add]; ring
  have hn2 : Real.exp t^2 - 1 ≠ 0 := by
    rw [← he]; exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr (by linarith)))
  simp only [ratioF, ratioG, G_eq_F (by omega : 1 ≤ 0+1) ht, G_zero_eq ht,
    F_one ht, F_two ht, F_three ht, F_zero, Real.exp_neg]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp; ring
  · field_simp; ring


private lemma ratio_low {t : ℝ} (ht : 0 < t) :
    ratioF 0 t = 1 + F 0 t ∧
    ratioF 1 t = 1 + 2 * F 0 t ∧
    ratioF 2 t = 1 + 4 * F 0 t - 2 * F 0 (2*t) ∧
    ratioG 0 t = F 0 t := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have hp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have he : Real.exp (2*t) = Real.exp t^2 := by rw [two_mul, Real.exp_add]; ring
  have hn2 : Real.exp t^2 - 1 ≠ 0 := by
    rw [← he]; exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr (by linarith)))
  obtain ⟨h0, h1, h2, hg⟩ := ratio_closed_forms ht
  rw [h0, h1, h2, hg]
  simp only [F_zero, he, Real.exp_neg]
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · field_simp

private lemma hasDerivAt_F (i : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (F i) (-F (i+1) t) t := by
  have hh := ((contDiffOn_F i).contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)
  convert hh.hasDerivAt using 1
  have hd := iteratedDeriv_F i 1 t
  simpa using hd.symm

private lemma iteratedDeriv_scaled_F (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (fun x => F 0 (2*x)) t =
      (-1 : ℝ)^k * 2^k * F k (2*t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun x => F 0 (2*x)) =ᶠ[𝓝 t]
        (fun x => (-1 : ℝ)^k * 2^k * F k (2*x)) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact ih hx
    have hd := ((hasDerivAt_F k (by linarith : 0 < 2*t)).comp t
      ((hasDerivAt_id t).const_mul 2)).const_mul ((-1 : ℝ)^k * 2^k)
    change HasDerivAt (fun x => (-1:ℝ)^k * 2^k * F k (2*x)) _ t at hd
    rw [he.deriv_eq, hd.deriv]
    simp only [pow_succ]
    ring

private lemma even_moment_le (k : ℕ) {t : ℝ} (ht : 0 < t) :
    2^k * F k (2*t) ≤ F k t := by
  let f : ℕ → ℝ := fun n => ((n+1 : ℕ) : ℝ)^k * Real.exp (-((n+1 : ℕ) : ℝ)*t)
  have hs : Summable f := by
    have hh := (Real.summable_pow_mul_exp_neg_nat_mul k ht).comp_injective (add_left_injective 1)
    convert hh using 1
    ext n
    dsimp [f, Function.comp_def]
    push_cast
    congr 2 <;> ring
  have hh := tsum_comp_le_tsum_of_inj hs (fun n => by dsimp [f]; positivity)
    (i := fun n : ℕ => 2*n+1) (by intro a b h; dsimp at h; omega)
  rw [← F_eq_tsum k ht] at hh
  have ht2 : 0 < 2*t := by linarith
  have hterm (n : ℕ) :
      2^k * (((n+1 : ℕ) : ℝ)^k * Real.exp (-((n+1 : ℕ) : ℝ)*(2*t))) = f (2*n+1) := by
    dsimp [f]
    push_cast
    rw [show (2:ℝ)*n+1+1 = 2*(n+1) by ring, mul_pow]
    rw [show -(n+1 : ℝ)*(2*t) = -(2*(n+1))*t by ring]
    ring
  rw [F_eq_tsum k ht2, ← tsum_mul_left]
  simpa only [hterm, Function.comp_def] using hh

private lemma cm_congr {f g : ℝ → ℝ}
    (hf : CompletelyMonotoneOn f) (hg : ContDiffOn ℝ ⊤ g (Ioi 0))
    (he : ∀ t, 0 < t → g t = f t) : CompletelyMonotoneOn g := by
  refine ⟨hg, ?_⟩
  intro k t ht
  have hh : g =ᶠ[𝓝 t] f := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact he x hx
  rw [hh.iteratedDeriv_eq k]
  exact hf.2 k t ht

private lemma cm_F_zero : CompletelyMonotoneOn (F 0) := by
  apply cm_of_nonnegative_exponential_expansion (c := fun _ => 1)
    (r := fun n => ((n+1 : ℕ) : ℝ)) (contDiffOn_F 0)
  · intro k t ht
    simpa only [iteratedDeriv_F, zero_add, one_mul] using
      congrArg (fun x : ℝ => (-1:ℝ)^k*x) (F_eq_tsum k ht)
  · intro n; norm_num
  · intro n; positivity

private lemma cm_affine (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    CompletelyMonotoneOn (fun t => a + c*F 0 t) := by
  refine ⟨contDiffOn_const.add (contDiffOn_const.mul (contDiffOn_F 0)), ?_⟩
  intro k t ht
  by_cases hk : k=0
  · subst k; simpa using add_nonneg ha (mul_nonneg hc (F_pos 0 ht).le)
  rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
    iteratedDeriv_F]
  have hs : (-1:ℝ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℝ)^k * (-1)^k) * (c * F k t) := by simp only [zero_add]; ring
    _ = c * F k t := by rw [hs, one_mul]
    _ ≥ 0 := mul_nonneg hc (F_pos k ht).le

private lemma cm_ratio_two : CompletelyMonotoneOn (ratioF 2) := by
  refine ⟨contDiffOn_ratioF 2, ?_⟩
  intro k t ht
  by_cases hk : k=0
  · subst k
    simpa [ratioF] using div_nonneg (F_pos 3 ht).le (F_pos 2 ht).le
  have he : ratioF 2 =ᶠ[𝓝 t] (fun x => 1 + (4*F 0 x - 2*F 0 (2*x))) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    linarith [(ratio_low hx).2.2.1]
  rw [he.iteratedDeriv_eq k, iteratedDeriv_const_add (by omega)]
  have hsmooth := (contDiffOn_F 0).contDiffAt (isOpen_Ioi.mem_nhds ht)
  have hscaled : ContDiffAt ℝ k (fun x => F 0 (2*x)) t :=
    ((contDiffOn_F 0).contDiffAt (isOpen_Ioi.mem_nhds (by linarith : 0 < 2*t))).of_le
      (by simp) |>.comp t (by fun_prop)
  have hleft : ContDiffAt ℝ k (fun x => 4*F 0 x) t :=
    contDiffAt_const.mul (hsmooth.of_le (by simp))
  have hright : ContDiffAt ℝ k (fun x => 2*F 0 (2*x)) t :=
    contDiffAt_const.mul hscaled
  rw [iteratedDeriv_fun_sub hleft hright,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_F, iteratedDeriv_scaled_F k ht]
  have hs : (-1:ℝ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  have heven := even_moment_le k ht
  have hf := (F_pos k ht).le
  simp only [zero_add]
  calc
    _ = ((-1:ℝ)^k * (-1)^k) * (4 * F k t - 2 * (2^k * F k (2*t))) := by ring
    _ = 4 * F k t - 2 * (2^k * F k (2*t)) := by rw [hs, one_mul]
    _ ≥ 0 := by nlinarith

/-- The two reciprocal families have completely monotone ratios at every index at most two. -/
theorem cm_of_le_two (i : ℕ) (hi : i ≤ 2) :
    CompletelyMonotoneOn (ratioF i) ∧ CompletelyMonotoneOn (ratioG i) := by
  have hF : CompletelyMonotoneOn (ratioF i) := by
    interval_cases i
    · exact cm_congr (cm_affine 1 1 (by norm_num) (by norm_num)) (contDiffOn_ratioF 0)
        (fun t ht => by simpa using (ratio_low ht).1)
    · exact cm_congr (cm_affine 1 2 (by norm_num) (by norm_num)) (contDiffOn_ratioF 1)
        (fun t ht => (ratio_low ht).2.1)
    · exact cm_ratio_two
  refine ⟨hF, ?_⟩
  by_cases hz : i=0
  · subst i
    exact cm_congr cm_F_zero (contDiffOn_ratioG 0) (fun t ht => (ratio_low ht).2.2.2)
  · exact cm_congr hF (contDiffOn_ratioG i) (fun t ht => ratioG_eq_ratioF (by omega) ht)

end D5.S3.Analytic.ExpRatioCM.Positive
