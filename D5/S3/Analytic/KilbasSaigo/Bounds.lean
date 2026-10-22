/- GID: D5/S3/Analytic/KilbasSaigo/Bounds
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Bounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Basic, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Mul, mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: Positivity and hyperbolic bounds from scaling equations and affine differential equations. -/

import D5.S3.Analytic.KilbasSaigo.Series
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory
open scoped Topology
open D5.S3.Analytic.KilbasSaigo.Defs D5.S3.Analytic.KilbasSaigo.Series

namespace D5.S3.Analytic.KilbasSaigo.Bounds

/-- A positive forcing and a nonnegative contraction kernel exclude a nonpositive minimum. -/
private lemma positive_of_scaling {f c p K L : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0))
    (hc : ∀ x ≥ 0, 0 < c x) (hp : ∀ x ≥ 0, 0 < p x)
    (hK : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ K r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, L r ∈ Icc (0 : ℝ) 1)
    (heq : ∀ x ≥ 0, c x * f x = p x +
      ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra hn
  have hn : f x ≤ 0 := le_of_not_gt hn
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx)
    (hf.mono (fun z hz => hz.1))
  have hyf : f y ≤ 0 := (hmin ⟨hx, le_rfl⟩).trans hn
  have hi : 0 ≤ ∫ r in Ioo (0 : ℝ) 1, (f (L r * y) - f y) * K r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply mul_nonneg _ (hK r hr)
    apply sub_nonneg.mpr
    apply hmin
    exact ⟨mul_nonneg (hL r hr).1 hy.1,
      (mul_le_of_le_one_left hy.1 (hL r hr).2).trans hy.2⟩
  have := heq y hy.1
  have := mul_nonpos_of_nonneg_of_nonpos (hc y hy.1).le hyf
  linarith [hp y hy.1]

/-- A positive source in a degenerate first-order equation preserves strict positivity. -/
private lemma positive_of_ode {f f' c p : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hf0 : 0 < f 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hc : ∀ x ≥ 0, 0 < c x) (hp : ∀ x ≥ 0, 0 < p x)
    (heq : ∀ x ≥ 0, b * x * f' x + c x * f x = p x) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra hn
  have hn : f x ≤ 0 := le_of_not_gt hn
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx)
    hcont.continuousOn
  have hyf : f y ≤ 0 := (hmin ⟨hx, le_rfl⟩).trans hn
  have hy0 : 0 < y := lt_of_le_of_ne hy.1 (by rintro rfl; linarith)
  have ht : (0 : ℝ) - y ∈ posTangentConeAt (Icc 0 x) y := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    exact (convex_Icc 0 x).segment_subset hy ⟨le_rfl, hx⟩
  have hd := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hf y).hasFDerivAt.hasFDerivWithinAt ht
  have hd' : f' y ≤ 0 := by
    change 0 ≤ (0 - y) * f' y at hd
    nlinarith
  have ht1 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hb hy0).le hd'
  have ht2 := mul_nonpos_of_nonneg_of_nonpos (hc y hy.1).le hyf
  linarith [heq y hy.1, hp y hy.1]

/-- Monotonicity and convexity turn a scaling equation into hyperbolic bounds. -/
private lemma hyperbolic_of_scaling {f K L : ℝ → ℝ} {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hf0 : f 0 = 1)
    (hanti : AntitoneOn f (Ici 0)) (hconv : ConvexOn ℝ (Ici 0) f)
    (hK : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ K r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmoment : ∫ r in Ioo (0 : ℝ) 1, (1 - L r) * K r = q - p)
    (heq : ∀ x ≥ 0, (p + x) * f x = p +
      ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) :
    ∀ x ≥ 0, p / (p + x) ≤ f x ∧ f x ≤ q / (q + x) := by
  intro x hx
  have hpoint (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      0 ≤ (f (L r * x) - f x) * K r ∧
      (f (L r * x) - f x) * K r ≤ (1 - f x) * ((1 - L r) * K r) := by
    have hscale := hL r hr
    have hd := hanti (mul_nonneg hscale.1 hx) hx
      (mul_le_of_le_one_left hx hscale.2)
    have hc := hconv.2 (show (0 : ℝ) ∈ Ici 0 by simp) hx
      (sub_nonneg.mpr hscale.2) hscale.1 (by ring : 1 - L r + L r = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, hf0, mul_one] at hc
    refine ⟨mul_nonneg (sub_nonneg.mpr hd) (hK r hr), ?_⟩
    have := mul_le_mul_of_nonneg_right (show f (L r * x) - f x ≤
      (1 - f x) * (1 - L r) by nlinarith) (hK r hr)
    nlinarith
  have hi0 : 0 ≤ ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hpoint r hr).1
  have hi1 : (∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) ≤
      (1 - f x) * (q - p) := by
    rw [← hmoment, ← integral_const_mul]
    apply integral_mono_of_nonneg _ (hint.const_mul (1 - f x))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hpoint r hr).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hpoint r hr).1
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < p + x)).mpr
    nlinarith [heq x hx]
  · apply (le_div_iff₀ (by linarith : 0 < q + x)).mpr
    nlinarith [heq x hx]

/-- A decreasing convex solution of the affine ODE satisfies both hyperbolic bounds. -/
private lemma hyperbolic_of_ode {f f' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hf0 : f 0 = 1)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hneg : ∀ x ≥ 0, f' x ≤ 0) (hconv : ConvexOn ℝ (Ici 0) f)
    (heq : ∀ x ≥ 0, b * x * f' x + (a + x) * f x = a) :
    ∀ x ≥ 0, a / (a + x) ≤ f x ∧ f x ≤ (a + b) / (a + b + x) := by
  intro x hx
  have htan : f x - x * f' x ≤ 1 := by
    rcases hx.eq_or_lt with rfl | hxpos
    · simp [hf0]
    · have ht := hconv.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici 0 by simp) hx hxpos (hf x)
      rw [slope_def_field, hf0, sub_zero] at ht
      have ht := (div_le_iff₀ hxpos).mp ht
      nlinarith
  have hs := heq x hx
  have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb.le hx) (hneg x hx)
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < a + x)).mpr
    nlinarith
  · apply (le_div_iff₀ (by linarith : 0 < a + b + x)).mpr
    nlinarith [mul_le_mul_of_nonneg_left htan hb.le]


private lemma phi_one {m l s : ℝ} (hm : 0 < m) (hl : m - 1 < l) (hs : 0 ≤ s) :
    phi 1 m l s = 1 + (l - m) + m * s := by
  have hpos : 0 < 1 + (l - m) + m * s := by nlinarith [mul_nonneg hm.le hs]
  unfold phi
  simp only [one_mul]
  rw [Real.Gamma_add_one hpos.ne', mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hpos).ne']

private lemma ode_one_base {m l : ℝ} (hm : 0 < m) (hl : m - 1 < l) (x : ℝ) :
    -m * x * g 1 m l 1 x + (1 + (l - m) + x) * g 1 m l 0 x = 1 + (l - m) := by
  have hl' : m - 1 / (1 : ℝ) < l := by simpa using hl
  let a := 1 + (l - m)
  have hc (n : ℕ) : (a + m * ((n : ℝ) + 1)) * ksCoeff 1 m l (n + 1) = ksCoeff 1 m l n := by
    rw [ksCoeff_succ, phi_one hm hl (by positivity)]
    have hpos : 0 < a + m * ((n : ℝ) + 1) := by dsimp [a]; nlinarith [mul_nonneg hm.le (Nat.cast_nonneg n)]
    change (a + m * ((n : ℝ) + 1)) * (_ / (a + m * ((n : ℝ) + 1))) = _
    exact mul_div_cancel₀ _ hpos.ne'
  have hd (n : ℕ) : gCoeff 1 m l 1 n = ((n : ℝ) + 1) * ksCoeff 1 m l (n + 1) := by
    rw [← gCoeff_step 1 m l 0 n]
    congr 1
    simp only [gCoeff, Nat.add_zero]
    rw [div_self (by positivity : (n + 1).factorial ≠ (0 : ℝ)), one_mul]
  have h0 : HasSum (fun n : ℕ => ksCoeff 1 m l n * (-x) ^ n) (g 1 m l 0 x) := by
    rw [← kilbasSaigo_neg_eq_g0]
    exact (summable_kilbasSaigo zero_lt_one hm hl' (-x)).hasSum
  have htail : HasSum (fun n : ℕ => ksCoeff 1 m l (n + 1) * (-x) ^ (n + 1))
      (g 1 m l 0 x - 1) := by
    have ht := ((summable_nat_add_iff 1).mpr h0.summable).hasSum
    convert ht using 1
    have ht' := h0.summable.tsum_eq_zero_add
    have hz : ksCoeff 1 m l 0 = 1 := by simp [ksCoeff]
    simp only [pow_zero, mul_one, hz] at ht'
    rw [h0.tsum_eq] at ht'
    linarith
  have h1 := (summable_gCoeff zero_lt_one hm hl' 1 (-x)).hasSum
  have H := ((h1.mul_left (m * x)).sub (h0.mul_left x)).sub (htail.mul_left a)
  have Hz : HasSum (fun _ : ℕ => (0 : ℝ))
      (m * x * g 1 m l 1 x - x * g 1 m l 0 x - a * (g 1 m l 0 x - 1)) := by
    convert H using 1
    · ext n
      rw [hd, pow_succ]
      have h := congrArg (fun z : ℝ => z * x * (-x) ^ n) (hc n)
      nlinarith
    · rfl
  have hh := Hz.unique hasSum_zero
  dsimp [a] at hh
  nlinarith

private lemma ode_one_succ {m l : ℝ} (hm : 0 < m) (hl : m - 1 < l) (k : ℕ) (x : ℝ) :
    -m * x * g 1 m l (k + 2) x +
      (1 + (l - m) + m * ((k : ℝ) + 1) + x) * g 1 m l (k + 1) x =
        ((k : ℝ) + 1) * g 1 m l k x := by
  have hl' : m - 1 / (1 : ℝ) < l := by simpa using hl
  induction k generalizing x with
  | zero =>
    have hD := (((hasDerivAt_id x).const_mul (-m)).mul (hasDerivAt_g zero_lt_one hm hl' 1 x)).add
      (((hasDerivAt_id x).const_add (1 + (l - m))).mul (hasDerivAt_g zero_lt_one hm hl' 0 x))
    have hE : HasDerivAt (fun _ : ℝ => 1 + (l - m))
        ((-m * g 1 m l 1 x + (-m * x) * (-g 1 m l 2 x)) +
          (1 * g 1 m l 0 x + (1 + (l - m) + x) * (-g 1 m l 1 x))) x := by
      simpa only [id_eq, mul_one, Nat.reduceAdd] using
        hD.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => (ode_one_base hm hl y).symm))
    have hval := hE.unique (hasDerivAt_const x (1 + (l - m)))
    simp only [Nat.cast_zero, zero_add] at *
    nlinarith
  | succ k ih =>
    have hD := (((hasDerivAt_id x).const_mul (-m)).mul (hasDerivAt_g zero_lt_one hm hl' (k + 2) x)).add
      (((hasDerivAt_id x).const_add (1 + (l - m) + m * ((k : ℝ) + 1))).mul
        (hasDerivAt_g zero_lt_one hm hl' (k + 1) x))
    have hE := hD.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => (ih y).symm))
    have hval := hE.unique ((hasDerivAt_g zero_lt_one hm hl' k x).const_mul ((k : ℝ) + 1))
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd,
      id_eq, mul_one, one_mul] at hval ⊢
    linear_combination -hval

private lemma g_positive_one {m l : ℝ} (hm : 0 < m) (hl : m - 1 < l) (k : ℕ) :
    ∀ x ≥ 0, 0 < g 1 m l k x := by
  have hl' : m - 1 / (1 : ℝ) < l := by simpa using hl
  have ha : 0 < 1 + (l - m) := by linarith
  induction k with
  | zero =>
    apply positive_of_ode hm (g_zero_pos zero_lt_one hm hl' 0)
      (hasDerivAt_g zero_lt_one hm hl' 0)
      (fun x hx => by linarith : ∀ x ≥ 0, 0 < 1 + (l - m) + x)
      (fun _ _ => ha)
    intro x hx
    have h := ode_one_base hm hl x
    nlinarith
  | succ k ih =>
    apply positive_of_ode hm (g_zero_pos zero_lt_one hm hl' (k + 1))
      (hasDerivAt_g zero_lt_one hm hl' (k + 1))
      (fun x hx => by positivity : ∀ x ≥ 0, 0 < 1 + (l - m) + m * ((k : ℝ) + 1) + x)
      (fun x hx => mul_pos (by positivity : 0 < (k : ℝ) + 1) (ih x hx))
    intro x hx
    have h := ode_one_succ hm hl k x
    simpa only [Nat.add_assoc, Nat.reduceAdd, mul_neg, neg_mul] using h

private lemma antitone_g {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ)
    (hpos : ∀ x ≥ 0, 0 < g α m l (k + 1) x) : AntitoneOn (g α m l k) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (continuous_g hα hm hl k).continuousOn
    (fun x _ => (hasDerivAt_g hα hm hl k x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  exact neg_nonpos.mpr (hpos x hx').le

private lemma convex_g0 {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (hpos : ∀ x ≥ 0, 0 < g α m l 2 x) :
    ConvexOn ℝ (Ici 0) (g α m l 0) := by
  have hm1 := antitone_g hα hm hl 1 hpos
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) (continuous_g hα hm hl 0).continuousOn
    (fun x _ => (hasDerivAt_g hα hm hl 0 x).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hasDerivAt_g hα hm hl 0 x).deriv, (hasDerivAt_g hα hm hl 0 y).deriv]
  exact neg_le_neg (hm1 (interior_subset hx) (interior_subset hy) hxy)

/-- Both hyperbolic bounds at the endpoint parameter alpha equal to one. -/
theorem bounds_one {m l x : ℝ} (hm : 0 < m) (hl : m - 1 < l) (hx : 0 ≤ x) :
    phi 1 m l 0 / (phi 1 m l 0 + x) ≤ g 1 m l 0 x ∧
      g 1 m l 0 x ≤ phi 1 m l 1 / (phi 1 m l 1 + x) := by
  have hl' : m - 1 / (1 : ℝ) < l := by simpa using hl
  have hf0 : g 1 m l 0 0 = 1 := by simp [g_zero, ksCoeff]
  have heq : ∀ y ≥ 0, m * y * (-g 1 m l 1 y) + (1 + (l - m) + y) * g 1 m l 0 y =
      1 + (l - m) := by
    intro y hy
    nlinarith [ode_one_base hm hl y]
  have h := hyperbolic_of_ode (by linarith : 0 < 1 + (l - m)) hm hf0
    (hasDerivAt_g zero_lt_one hm hl' 0)
    (fun y hy => neg_nonpos.mpr (g_positive_one hm hl 1 y hy).le)
    (convex_g0 zero_lt_one hm hl' (g_positive_one hm hl 2)) heq x hx
  simpa only [phi_one hm hl (show (0 : ℝ) ≤ 0 by rfl), phi_one hm hl zero_le_one,
    mul_zero, mul_one, add_zero] using h

end D5.S3.Analytic.KilbasSaigo.Bounds
