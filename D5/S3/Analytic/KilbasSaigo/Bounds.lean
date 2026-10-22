/- GID: D5/S3/Analytic/KilbasSaigo/Bounds
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Bounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.Normed.Module.FiniteDimension, mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Basic, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Mul, mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, mathlib/module/Mathlib.Analysis.Calculus.DSlope, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Positivity and hyperbolic bounds from scaling equations and affine differential equations. -/

import D5.S3.Analytic.KilbasSaigo.Series
import D5.S3.Analytic.KilbasSaigo.Certificate
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory
open scoped Topology
open D5.S3.Analytic.KilbasSaigo.Defs D5.S3.Analytic.KilbasSaigo.Series

noncomputable section
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

namespace FractionalCertificate
open D5.S3.Analytic.KilbasSaigo.Certificate
open D5.S3.Analytic.KummerRatio.BetaIntegral

private def slopePower (q r : ℝ) : ℝ := dslope (fun t : ℝ => t ^ q) 1 r

private def primitive (α a q r : ℝ) : ℝ :=
  slopePower q r * r ^ (a + α) * (1 - r) ^ (1 - α)

private def weight (α a r : ℝ) : ℝ := r ^ (a + α - 1) * (1-r) ^ (-α)

private def regularIntegrand (α a q r : ℝ) : ℝ := slopePower q r * weight α a r

private lemma slopePower_continuous {q : ℝ} (hq : 0 ≤ q) :
    Continuous (slopePower q) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 1
  · subst r
    exact continuousAt_dslope_same.mpr
      (Real.differentiableAt_rpow_const_of_ne q one_ne_zero)
  · exact (continuousAt_dslope_of_ne hr).mpr
      (Real.continuous_rpow_const hq).continuousAt

private lemma slopePower_identity (q r : ℝ) : (1-r) * slopePower q r = 1-r^q := by
  have h := sub_smul_dslope (fun t : ℝ => t ^ q) 1 r
  simp only [smul_eq_mul, Real.one_rpow] at h
  dsimp [slopePower]
  linarith

private lemma primitive_continuous {α a q : ℝ} (hα : α < 1) (ha : 0 < a + α)
    (hq : 0 ≤ q) : Continuous (primitive α a q) := by
  exact ((slopePower_continuous hq).mul
    (Real.continuous_rpow_const ha.le)).mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 1-α)).comp
        (continuous_const.sub continuous_id))

private lemma primitive_zero {α a q : ℝ} (ha : 0 < a+α) : primitive α a q 0 = 0 := by
  simp [primitive, Real.zero_rpow ha.ne']

private lemma primitive_one {α a q : ℝ} (hα : α < 1) : primitive α a q 1 = 0 := by
  simp [primitive, Real.zero_rpow (by linarith : 1-α ≠ 0)]

private lemma primitive_eq {α a q r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    primitive α a q r =
      (r^(a+α) - r^(a+q+α)) * (1-r)^(-α) := by
  have hs := slopePower_identity q r
  have hp : (1-r)^(1-α) = (1-r)*(1-r)^(-α) := by
    rw [show 1-α = 1+(-α) by ring, Real.rpow_add (by linarith), Real.rpow_one]
  have hq : r^(a+q+α) = r^(a+α)*r^q := by
    rw [show a+q+α = (a+α)+q by ring, Real.rpow_add hr]
  rw [primitive, hp, hq]
  calc
    _ = ((1-r)*slopePower q r)*r^(a+α)*(1-r)^(-α) := by ring
    _ = _ := by rw [hs]; ring

private lemma weight_integrable {α a : ℝ} (hα : α < 1) (ha : 0 < a+α) :
    IntervalIntegrable (weight α a) volume 0 1 := by
  convert intervalIntegrable_beta ha (by linarith : 0 < 1-α) using 1
  congr 1
  ext r
  dsimp [weight]
  congr 2 <;> ring

private lemma regularIntegrand_integrable {α a q : ℝ} (hα : α < 1) (ha : 0 < a+α)
    (hq : 0 ≤ q) : IntervalIntegrable (regularIntegrand α a q) volume 0 1 := by
  exact (weight_integrable hα ha).continuousOn_mul
    (slopePower_continuous hq).continuousOn

private lemma incrementIntegrand_eq {α a q r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    incrementIntegrand α a q r =
      α / Real.Gamma (1-α) * regularIntegrand α a q r := by
  have hs := slopePower_identity q r
  have hp : (1-r)^(-α) = (1-r)*(1-r)^(-1-α) := by
    rw [show -α = 1+(-1-α) by ring, Real.rpow_add (by linarith), Real.rpow_one]
  dsimp [incrementIntegrand, kernel, regularIntegrand, weight]
  rw [hp]
  calc
    _ = α / Real.Gamma (1-α) * ((1-r)*slopePower q r) *
      r^(a+α-1) * (1-r)^(-1-α) := by rw [hs]; ring
    _ = _ := by ring

private lemma incrementIntegrand_integrable {α a q : ℝ} (hα : α < 1) (ha : 0 < a+α)
    (hq : 0 ≤ q) : IntervalIntegrable (incrementIntegrand α a q) volume 0 1 := by
  have hi := (regularIntegrand_integrable hα ha hq).const_mul
    (α / Real.Gamma (1-α))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hi ⊢
  exact hi.congr_fun (fun r hr => (incrementIntegrand_eq hr.1 hr.2).symm)
    measurableSet_Ioo

private lemma hasDerivAt_primitive {α a q r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (primitive α a q)
      (α * regularIntegrand α a q r + a * weight α a r -
        (a+q) * weight α (a+q) r) r := by
  have hd1 := Real.hasDerivAt_rpow_const (x := r) (p := a+α) (Or.inl hr.ne')
  have hd2 := Real.hasDerivAt_rpow_const (x := r) (p := a+q+α) (Or.inl hr.ne')
  have hd3 := ((hasDerivAt_id r).const_sub 1).rpow_const
    (p := -α) (Or.inl (by linarith : 1-r ≠ 0))
  have hd := (hd1.sub hd2).mul hd3
  have hloc : (fun t : ℝ => (t^(a+α)-t^(a+q+α))*(1-t)^(-α)) =ᶠ[𝓝 r]
      primitive α a q := by
    filter_upwards [Ioo_mem_nhds hr hr1] with t ht
    exact (primitive_eq ht.1 ht.2).symm
  have hs := slopePower_identity q r
  have hp : (1-r)^(-α) = (1-r)*(1-r)^(-α-1) := by
    nth_rw 1 [show -α = 1+(-α-1) by ring]
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hpow1 : r^(a+α) = r*r^(a+α-1) := by
    nth_rw 1 [show a+α = 1+(a+α-1) by ring]
    rw [Real.rpow_add hr, Real.rpow_one]
  have hpow2 : r^(a+q+α-1) = r^(a+α-1)*r^q := by
    rw [show a+q+α-1 = (a+α-1)+q by ring, Real.rpow_add hr]
  have hpow3 : r^(a+q+α) = r*r^(a+α-1)*r^q := by
    rw [show a+q+α = (a+α)+q by ring, Real.rpow_add hr, hpow1]
  convert hd.congr_of_eventuallyEq hloc.symm using 1
  dsimp [regularIntegrand, weight]
  rw [hp, hpow1, hpow2, hpow3]
  have hm := congrArg (fun z : ℝ => z * r^(a+α-1) * (1-r)^(-α-1) * α) hs
  nlinarith only [hm]

private lemma integral_weight {α a : ℝ} (hα : α < 1) (ha : 0 < a+α) :
    (∫ r in (0:ℝ)..1, weight α a r) =
      Real.Gamma (a+α) * Real.Gamma (1-α) / Real.Gamma (a+1) := by
  convert integral_beta ha (by linarith : 0 < 1-α) using 1
  · congr 1
    ext r
    dsimp [weight]
    congr 2 <;> ring
  · congr 2
    ring

private lemma certificate_full {α a q : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 < a) (hq : 0 ≤ q) :
    (∫ r in (0:ℝ)..1, incrementIntegrand α a q r) =
      Real.Gamma (a+q+α) / Real.Gamma (a+q) -
        Real.Gamma (a+α) / Real.Gamma a := by
  by_cases hq0 : q = 0
  · exact D5.S3.Analytic.KilbasSaigo.Certificate.certificate α a q hq0
  have haα : 0 < a+α := by linarith
  have haq : 0 < a+q := by linarith
  have haqα : 0 < (a+q)+α := by linarith
  have hi := regularIntegrand_integrable hα1 haα hq
  have hw := weight_integrable hα1 haα
  have hv := weight_integrable hα1 haqα
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (primitive_continuous hα1 haα hq).continuousOn
    (fun r hr => hasDerivAt_primitive hr.1 hr.2)
    (((hi.const_mul α).add (hw.const_mul a)).sub (hv.const_mul (a+q)))
  rw [primitive_one hα1, primitive_zero haα, sub_self,
    intervalIntegral.integral_sub ((hi.const_mul α).add (hw.const_mul a))
      (hv.const_mul (a+q)),
    intervalIntegral.integral_add (hi.const_mul α) (hw.const_mul a)] at hf
  simp_rw [intervalIntegral.integral_const_mul] at hf
  have hwval : a * (∫ r in (0:ℝ)..1, weight α a r) =
      Real.Gamma (1-α) * (Real.Gamma (a+α) / Real.Gamma a) := by
    rw [integral_weight hα1 haα, Real.Gamma_add_one ha.ne']
    field_simp
  have hvval : (a+q) * (∫ r in (0:ℝ)..1, weight α (a+q) r) =
      Real.Gamma (1-α) * (Real.Gamma (a+q+α) / Real.Gamma (a+q)) := by
    rw [integral_weight hα1 haqα, Real.Gamma_add_one haq.ne']
    field_simp
  rw [hwval, hvval] at hf
  calc
    (∫ r in (0:ℝ)..1, incrementIntegrand α a q r) =
        ∫ r in (0:ℝ)..1, α / Real.Gamma (1-α) * regularIntegrand α a q r := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro r hr
      exact incrementIntegrand_eq hr.1 hr.2
    _ = α / Real.Gamma (1-α) * (∫ r in (0:ℝ)..1, regularIntegrand α a q r) :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by
      have hg : Real.Gamma (1-α) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by linarith : 0 < 1-α)).ne'
      rw [div_mul_eq_mul_div, div_eq_iff hg]
      nlinarith [hf]

private theorem integrableOn_increment {α a q : ℝ} (hα1 : α < 1)
    (ha : 0 < a+α) (hq : 0 ≤ q) :
    IntegrableOn (incrementIntegrand α a q) (Ioo 0 1) volume :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (incrementIntegrand_integrable hα1 ha hq)

private theorem certificate_set {α a q : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 < a) (hq : 0 ≤ q) :
    (∫ r in Ioo (0:ℝ) 1, incrementIntegrand α a q r) =
      Real.Gamma (a+q+α) / Real.Gamma (a+q) -
        Real.Gamma (a+α) / Real.Gamma a := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact certificate_full hα0 hα1 ha hq



open D5.S3.Analytic.KilbasSaigo.Series

private lemma kernel_measurable (α a : ℝ) : Measurable (kernel α a) := by
  unfold kernel
  fun_prop

private lemma lambda_measurable (b : ℝ) : Measurable (fun r : ℝ => r^b) := by
  fun_prop

private lemma kernel_nonneg {α a r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : r ∈ Ioo (0:ℝ) 1) : 0 ≤ kernel α a r := by
  unfold kernel
  exact mul_nonneg (mul_nonneg (div_nonneg hα0.le
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1-α)).le)
    (Real.rpow_nonneg hr.1.le _)) (Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _)

private lemma lambda_mem {b r : ℝ} (hb : 0 ≤ b) (hr : r ∈ Ioo (0:ℝ) 1) :
    r^b ∈ Icc (0:ℝ) 1 := by
  exact ⟨Real.rpow_nonneg hr.1.le _, Real.rpow_le_one hr.1.le hr.2.le hb⟩

private lemma kernel_firstMoment_integrable {α a b : ℝ} (hα1 : α < 1)
    (ha : 0 < a+α) (hb : 0 ≤ b) :
    IntegrableOn (fun r : ℝ => (1-r^b)*kernel α a r) (Ioo (0:ℝ) 1) := by
  exact integrableOn_increment hα1 ha hb

private lemma kernel_natural_moment {α m l : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hm : 0 < m) (hl : m-1/α < l) (n : ℕ) :
    (∫ r in Ioo (0:ℝ) 1,
      (1-(r^(α*m))^n)*kernel α (1+α*(l-m)) r) =
      phi α m l n - phi α m l 0 := by
  have hq : 0 ≤ α*m*(n:ℝ) := by positivity
  calc
    _ = ∫ r in Ioo (0:ℝ) 1,
        incrementIntegrand α (1+α*(l-m)) (α*m*(n:ℝ)) r := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp [incrementIntegrand]
      rw [← Real.rpow_mul_natCast hr.1.le (α*m) n]
    _ = _ := by
      rw [certificate_set hα0 hα1 (base_pos hα0 hl) hq]
      simp [phi]

private lemma kernel_data {α m l : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hm : 0 < m) (hl : m-1/α < l) :
    (∀ᵐ r ∂(volume.restrict (Ioo (0:ℝ) 1)),
      0 ≤ kernel α (1+α*(l-m)) r) ∧
    (∀ᵐ r ∂(volume.restrict (Ioo (0:ℝ) 1)),
      r^(α*m) ∈ Icc (0:ℝ) 1) ∧
    IntegrableOn (fun r : ℝ => (1-r^(α*m))*kernel α (1+α*(l-m)) r)
      (Ioo (0:ℝ) 1) := by
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact kernel_nonneg hα0 hα1 hr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact lambda_mem (mul_pos hα0 hm).le hr
  · exact kernel_firstMoment_integrable hα1
      (by linarith [base_pos hα0 hl]) (mul_pos hα0 hm).le

end FractionalCertificate

/-- A hierarchy of positive contraction equations has positive signed derivatives and hyperbolic bounds. -/
private lemma bounds_of_scaling_system {G : ℕ → ℝ → ℝ} {P : ℕ → ℝ} {K L : ℝ → ℝ}
    (hP : ∀ k, 0 < P k) (hzero : G 0 0 = 1)
    (hder : ∀ k x, HasDerivAt (G k) (-G (k + 1) x) x)
    (hK : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ K r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmoment : ∫ r in Ioo (0 : ℝ) 1, (1 - L r) * K r = P 1 - P 0)
    (heq0 : ∀ x ≥ 0, (P 0 + x) * G 0 x = P 0 +
      ∫ r in Ioo (0 : ℝ) 1, (G 0 (L r * x) - G 0 x) * K r)
    (heqS : ∀ k x, 0 ≤ x → (P (k + 1) + x) * G (k + 1) x =
      ((k : ℝ) + 1) * G k x + ∫ r in Ioo (0 : ℝ) 1,
        L r ^ (k + 1) * (G (k + 1) (L r * x) - G (k + 1) x) * K r) :
    (∀ k x, 0 ≤ x → 0 < G k x) ∧ AntitoneOn (G 0) (Ici 0) ∧
      ConvexOn ℝ (Ici 0) (G 0) ∧
      ∀ x ≥ 0, P 0 / (P 0 + x) ≤ G 0 x ∧ G 0 x ≤ P 1 / (P 1 + x) := by
  have hcont (k : ℕ) : Continuous (G k) :=
    continuous_iff_continuousAt.mpr (fun x => (hder k x).continuousAt)
  have hpos : ∀ k x, 0 ≤ x → 0 < G k x := by
    intro k
    induction k with
    | zero =>
      exact positive_of_scaling (hcont 0).continuousOn
        (fun x hx => by linarith [hP 0]) (fun _ _ => hP 0) hK hL heq0
    | succ k ih =>
      apply positive_of_scaling (K := fun r => L r ^ (k + 1) * K r) (L := L)
        (c := fun x => P (k + 1) + x) (p := fun x => ((k : ℝ) + 1) * G k x)
        (hcont (k + 1)).continuousOn
        (fun x hx => by linarith [hP (k + 1)])
        (fun x hx => mul_pos (by positivity : 0 < (k : ℝ) + 1) (ih x hx))
        (fun r hr => mul_nonneg (pow_nonneg (hL r hr).1 _) (hK r hr)) hL
      intro x hx
      rw [heqS k x hx]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by ring)
  have hanti (k : ℕ) : AntitoneOn (G k) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (hcont k).continuousOn
      (fun x _ => (hder k x).hasDerivWithinAt)
    intro x hx
    exact neg_nonpos.mpr (hpos (k + 1) x (interior_subset hx)).le
  have hconv : ConvexOn ℝ (Ici 0) (G 0) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) (hcont 0).continuousOn
      (fun x _ => (hder 0 x).differentiableAt.differentiableWithinAt)
    intro x hx y hy hxy
    rw [(hder 0 x).deriv, (hder 0 y).deriv]
    exact neg_le_neg (hanti 1 (interior_subset hx) (interior_subset hy) hxy)
  exact ⟨hpos, hanti 0, hconv,
    hyperbolic_of_scaling (hP 0) (hP 1) hzero (hanti 0) hconv hK hL hint hmoment heq0⟩

namespace ScalingWork

private lemma power_difference_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    |t ^ n - 1| ≤ (n : ℝ) * (1 - t) := by
  have h := abs_pow_sub_pow_le (a := t) (b := (1 : ℝ)) (n := n)
  simpa [abs_of_nonneg ht0, max_eq_right ht1, abs_of_nonpos (sub_nonpos.mpr ht1),
    mul_comm] using h

private lemma summable_degree_gCoeff {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) (x : ℝ) :
    Summable (fun n : ℕ => |gCoeff α m l k n * (-x) ^ n| * n) := by
  apply (summable_nat_add_iff 1).mp
  have hs := ((summable_gCoeff hα hm hl (k + 1) (-x)).norm).mul_right |x|
  convert hs using 1
  funext n
  rw [Real.norm_eq_abs, ← gCoeff_step α m l k n]
  simp only [Nat.cast_add, Nat.cast_one, pow_succ, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  ring

private lemma hasSum_integral_scaling {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) {K L : ℝ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => ∫ r in Ioo (0 : ℝ) 1,
      gCoeff α m l k n * (-x) ^ n * (L r ^ k * (L r ^ n - 1) * K r))
      (∫ r in Ioo (0 : ℝ) 1,
        L r ^ k * (g α m l k (L r * x) - g α m l k x) * K r) := by
  let d : ℕ → ℝ := fun n => gCoeff α m l k n * (-x) ^ n
  let w : ℝ → ℝ := fun r => (1 - L r) * K r
  let b : ℕ → ℝ → ℝ := fun n r => (|d n| * n) * w r
  have hs : Summable (fun n : ℕ => |d n| * n) := summable_degree_gCoeff hα hm hl k x
  apply hasSum_integral_of_dominated_convergence b
  · intro n
    apply Measurable.aestronglyMeasurable
    exact measurable_const.mul (((hLm.pow_const k).mul
      ((hLm.pow_const n).sub measurable_const)).mul hKm)
  · intro n
    filter_upwards [hK, hL] with r hrK hrL
    have hp := power_difference_bound hrL.1 hrL.2 n
    have hpow : L r ^ k ≤ 1 := pow_le_one₀ hrL.1 hrL.2
    have hn : 0 ≤ (n : ℝ) * (1 - L r) := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hrL.2)
    dsimp only [b, d, w]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (pow_nonneg hrL.1 k), abs_of_nonneg hrL.1, abs_of_nonneg hrK]
    calc
      _ ≤ (|gCoeff α m l k n| * |x| ^ n) *
          (1 * ((n : ℝ) * (1 - L r)) * K r) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul hpow hp (abs_nonneg _) zero_le_one) hrK)
          (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
      _ = _ := by ring
  · filter_upwards [] with r
    exact hs.mul_right (w r)
  · convert hint.const_mul (∑' n : ℕ, |d n| * n) using 1
    funext r
    exact (hs.hasSum.mul_right (w r)).tsum_eq
  · filter_upwards [] with r
    have hsum := ((summable_gCoeff hα hm hl k (-(L r * x))).hasSum.sub
      (summable_gCoeff hα hm hl k (-x)).hasSum).mul_left (L r ^ k * K r)
    convert hsum using 1
    · funext n
      rw [show -(L r * x) = L r * (-x) by ring, mul_pow]
      ring
    · simp only [g]
      ring

private lemma integrable_power_increment {K L : ℝ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1)) (n : ℕ) :
    IntegrableOn (fun r => (1 - L r ^ n) * K r) (Ioo (0 : ℝ) 1) := by
  apply (hint.const_mul (n : ℝ)).mono'
  · exact ((measurable_const.sub (hLm.pow_const n)).mul hKm).aestronglyMeasurable
  · filter_upwards [hK, hL] with r hrK hrL
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrK, abs_sub_comm]
    have h := mul_le_mul_of_nonneg_right (power_difference_bound hrL.1 hrL.2 n) hrK
    nlinarith

private lemma integral_weighted_moment {K L : ℝ → ℝ} {p : ℕ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmom : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, (1 - L r ^ n) * K r = p n - p 0)
    (k n : ℕ) :
    (∫ r in Ioo (0 : ℝ) 1, L r ^ k * (L r ^ n - 1) * K r) = p k - p (n + k) := by
  have he : (fun r => L r ^ k * (L r ^ n - 1) * K r) =
      (fun r => (1 - L r ^ k) * K r - (1 - L r ^ (n + k)) * K r) := by
    funext r
    rw [pow_add]
    ring
  rw [he, integral_sub (integrable_power_increment hKm hLm hK hL hint k)
    (integrable_power_increment hKm hLm hK hL hint (n + k)), hmom, hmom]
  ring

private lemma hasSum_scaling_moment {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) {K L : ℝ → ℝ} {p : ℕ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmom : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, (1 - L r ^ n) * K r = p n - p 0)
    (k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => gCoeff α m l k n * (-x) ^ n * (p k - p (n + k)))
      (∫ r in Ioo (0 : ℝ) 1,
        L r ^ k * (g α m l k (L r * x) - g α m l k x) * K r) := by
  have h := hasSum_integral_scaling hα hm hl hKm hLm hK hL hint k x
  simpa only [integral_const_mul, integral_weighted_moment hKm hLm hK hL hint hmom] using h

private lemma hasSum_degree_gCoeff {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * gCoeff α m l k n * (-x) ^ n)
      (-x * g α m l (k + 1) x) := by
  have h := ((summable_gCoeff hα hm hl (k + 1) (-x)).hasSum).mul_left (-x)
  have ht : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * gCoeff α m l k (n + 1) * (-x) ^ (n + 1))
      (-x * g α m l (k + 1) x) := by
    convert h using 1
    · funext n
      rw [Nat.cast_add, Nat.cast_one, gCoeff_step, pow_succ]
      ring
    · rfl
  simpa using (hasSum_nat_add_iff (f := fun n : ℕ =>
    (n : ℝ) * gCoeff α m l k n * (-x) ^ n) 1).mp ht

private lemma gCoeff_phi {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) (k n : ℕ) :
    phi α m l (n + k + 1) * gCoeff α m l (k + 1) n =
      ((n : ℝ) + k + 1) * gCoeff α m l k n := by
  simp only [gCoeff]
  rw [show n + (k + 1) = (n + k) + 1 by omega, Nat.factorial_succ, ksCoeff_succ]
  push_cast
  have hp := (phi_pos hα hm hl (show (0 : ℝ) ≤ n + k + 1 by positivity)).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

private lemma scaling_g_succ {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) {K L : ℝ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmom : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, (1 - L r ^ n) * K r =
      phi α m l n - phi α m l 0)
    (k : ℕ) (x : ℝ) :
    (phi α m l (k + 1) + x) * g α m l (k + 1) x =
      ((k : ℝ) + 1) * g α m l k x +
        ∫ r in Ioo (0 : ℝ) 1, L r ^ (k + 1) *
          (g α m l (k + 1) (L r * x) - g α m l (k + 1) x) * K r := by
  have hs0 := (summable_gCoeff hα hm hl k (-x)).hasSum
  have hs1 := (summable_gCoeff hα hm hl (k + 1) (-x)).hasSum
  have ht := (hs0.mul_left ((k : ℝ) + 1)).add (hasSum_degree_gCoeff hα hm hl k x)
  have hphi : HasSum (fun n : ℕ =>
      gCoeff α m l (k + 1) n * (-x) ^ n * phi α m l (n + k + 1))
      (((k : ℝ) + 1) * g α m l k x - x * g α m l (k + 1) x) := by
    convert ht using 1
    · funext n
      have h := congrArg (fun z : ℝ => z * (-x) ^ n) (gCoeff_phi hα hm hl k n)
      nlinarith
    · simp only [g]
      ring
  have hdiff := (hs1.mul_left (phi α m l (k + 1))).sub hphi
  have hmom' := hasSum_scaling_moment (p := fun n => phi α m l n) hα hm hl hKm hLm hK hL hint (by simpa only [Nat.cast_zero] using hmom) (k + 1) x
  have he : HasSum (fun n : ℕ => gCoeff α m l (k + 1) n * (-x) ^ n *
      (phi α m l (k + 1) - phi α m l (n + (k + 1))))
      (phi α m l (k + 1) * g α m l (k + 1) x -
        (((k : ℝ) + 1) * g α m l k x - x * g α m l (k + 1) x)) := by
    convert hdiff using 1
    · funext n
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
      ring
    · rfl
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc] at hmom' he
  have hval := hmom'.unique he
  push_cast at hval ⊢
  linarith

private lemma scaling_f {α m l : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hl : m - 1 / α < l) {K L : ℝ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L)
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ K r)
    (hL : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmom : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, (1 - L r ^ n) * K r =
      phi α m l n - phi α m l 0) (x : ℝ) :
    (phi α m l 0 + x) * g α m l 0 x = phi α m l 0 +
      ∫ r in Ioo (0 : ℝ) 1, (g α m l 0 (L r * x) - g α m l 0 x) * K r := by
  have hs := (summable_kilbasSaigo hα hm hl (-x)).hasSum
  change HasSum _ (kilbasSaigo α m l (-x)) at hs
  rw [kilbasSaigo_neg_eq_g0] at hs
  have ht := hs.mul_left (-x)
  have htail : HasSum (fun n : ℕ => phi α m l (n + 1) *
      ksCoeff α m l (n + 1) * (-x) ^ (n + 1)) (-x * g α m l 0 x) := by
    convert ht using 1
    funext n
    rw [ksCoeff_succ, pow_succ]
    have hp := (phi_pos hα hm hl (show (0 : ℝ) ≤ n + 1 by positivity)).ne'
    field_simp <;> ring
  have hphi := (hasSum_nat_add_iff (f := fun n : ℕ =>
    phi α m l n * ksCoeff α m l n * (-x) ^ n) 1).mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using htail)
  have hz : ksCoeff α m l 0 = 1 := by simp [ksCoeff]
  simp only [Finset.sum_range_one, Nat.cast_zero, hz, pow_zero, mul_one] at hphi
  have hdiff := (hs.mul_left (phi α m l 0)).sub hphi
  have hmom' := hasSum_scaling_moment (p := fun n => phi α m l n) hα hm hl hKm hLm hK hL hint (by simpa only [Nat.cast_zero] using hmom) 0 x
  have he : HasSum (fun n : ℕ => gCoeff α m l 0 n * (-x) ^ n *
      (phi α m l 0 - phi α m l (n + 0)))
      (phi α m l 0 * g α m l 0 x - (-x * g α m l 0 x + phi α m l 0)) := by
    convert hdiff using 1
    · funext n
      simp only [gCoeff, Nat.add_zero, add_zero,
        div_self (by positivity : (n.factorial : ℝ) ≠ 0), one_mul]
      ring
  simp only [Nat.cast_zero, Nat.add_zero, add_zero] at hmom' he
  have hval := hmom'.unique he
  simp only [pow_zero, one_mul] at hval
  linarith


end ScalingWork

private lemma fractional_system {α m l : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hm : 0 < m) (hl : m - 1 / α < l) :
    (∀ k x, 0 ≤ x → 0 < g α m l k x) ∧ AntitoneOn (g α m l 0) (Ici 0) ∧
      ConvexOn ℝ (Ici 0) (g α m l 0) ∧
      ∀ x ≥ 0, phi α m l 0 / (phi α m l 0 + x) ≤ g α m l 0 x ∧
        g α m l 0 x ≤ phi α m l 1 / (phi α m l 1 + x) := by
  let K := Certificate.kernel α (1 + α * (l - m))
  let L := fun r : ℝ => r ^ (α * m)
  obtain ⟨hK, hL, hint⟩ := FractionalCertificate.kernel_data hα hα1 hm hl
  have hmoment := FractionalCertificate.kernel_natural_moment hα hα1 hm hl
  have hKm : Measurable K := FractionalCertificate.kernel_measurable _ _
  have hLm : Measurable L := FractionalCertificate.lambda_measurable _
  have hs := bounds_of_scaling_system (G := g α m l) (P := fun k => phi α m l k)
    (K := K) (L := L)
    (fun k => phi_pos hα hm hl (Nat.cast_nonneg k))
    (by simp [g_zero, ksCoeff]) (hasDerivAt_g hα hm hl)
    (fun _ hr => FractionalCertificate.kernel_nonneg hα hα1 hr)
    (fun _ hr => FractionalCertificate.lambda_mem (mul_pos hα hm).le hr) hint
    (by simpa only [pow_one, Nat.cast_one, Nat.cast_zero] using hmoment 1)
    (fun x _ => by simpa only [Nat.cast_zero] using
      ScalingWork.scaling_f hα hm hl hKm hLm hK hL hint hmoment x)
    (fun k x _ => by simpa only [Nat.cast_add, Nat.cast_one] using
      ScalingWork.scaling_g_succ hα hm hl hKm hLm hK hL hint hmoment k x)
  simpa only [Nat.cast_zero, Nat.cast_one] using hs

/-- The first three signed derivatives are strictly positive on the negative-axis parameterization. -/
theorem pos_decreasing_convex {α m l x : ℝ} (hα : 0 < α) (hαle : α ≤ 1)
    (hm : 0 < m) (hl : m - 1 / α < l) (hx : 0 ≤ x) :
    0 < g α m l 0 x ∧ 0 < g α m l 1 x ∧ 0 < g α m l 2 x := by
  rcases lt_or_eq_of_le hαle with hlt | rfl
  · have h := (fractional_system hα hlt hm hl).1
    exact ⟨h 0 x hx, h 1 x hx, h 2 x hx⟩
  · have hl' : m - 1 < l := by simpa using hl
    exact ⟨g_positive_one hm hl' 0 x hx, g_positive_one hm hl' 1 x hx,
      g_positive_one hm hl' 2 x hx⟩

private lemma ratio_rewrite {p d x : ℝ} (hp : 0 < p) (hd : 0 < d) (hx : 0 ≤ x) :
    (p / d) / (p / d + x) = 1 / (1 + d / p * x) := by
  have hp0 := hp.ne'
  have hd0 := hd.ne'
  have h1 : p / d + x ≠ 0 := (add_pos_of_pos_of_nonneg (div_pos hp hd) hx).ne'
  have h2 : 1 + d / p * x ≠ 0 := (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (div_pos hd hp).le hx)).ne'
  field_simp

private lemma bounds_to_pinned {α m l x : ℝ}
    (hα : 0 < α) (hm : 0 < m) (hl : m - 1 / α < l) (hx : 0 ≤ x)
    (h : phi α m l 0 / (phi α m l 0 + x) ≤ g α m l 0 x ∧
      g α m l 0 x ≤ phi α m l 1 / (phi α m l 1 + x)) :
      1 / (1 + Real.Gamma (1 + α * (l - m)) /
        Real.Gamma (1 + α * (l - m + 1)) * x) ≤ kilbasSaigo α m l (-x) ∧
      kilbasSaigo α m l (-x) ≤ 1 / (1 + Real.Gamma (1 + α * l) /
        Real.Gamma (1 + α * (1 + l)) * x) := by
  have ha := base_pos hα hl
  have harg0 : 1 + α * (l - m) + α = 1 + α * (l - m + 1) := by ring
  have harg1 : 1 + α * (l - m) + α * m = 1 + α * l := by ring
  have harg2 : 1 + α * l + α = 1 + α * (1 + l) := by ring
  have hpos1 : 0 < 1 + α * l := by nlinarith [mul_pos hα hm]
  rw [kilbasSaigo_neg_eq_g0]
  simpa only [phi, mul_zero, add_zero, mul_one, harg0, harg1, harg2,
    ratio_rewrite (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + α * (l - m + 1)))
      (Real.Gamma_pos_of_pos ha) hx,
    ratio_rewrite (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + α * (1 + l)))
      (Real.Gamma_pos_of_pos hpos1) hx] using h

/-- The two hyperbolic bounds for the full parameter range. -/
theorem bounds {α m l x : ℝ} (hα : 0 < α) (hαle : α ≤ 1)
    (hm : 0 < m) (hl : m - 1 / α < l) (hx : 0 ≤ x) :
    1 / (1 + Real.Gamma (1 + α * (l - m)) /
      Real.Gamma (1 + α * (l - m + 1)) * x) ≤ kilbasSaigo α m l (-x) ∧
    kilbasSaigo α m l (-x) ≤ 1 / (1 + Real.Gamma (1 + α * l) /
      Real.Gamma (1 + α * (1 + l)) * x) := by
  apply bounds_to_pinned hα hm hl hx
  rcases lt_or_eq_of_le hαle with hlt | rfl
  · exact (fractional_system hα hlt hm hl).2.2.2 x hx
  · exact bounds_one hm (by simpa using hl) hx

end D5.S3.Analytic.KilbasSaigo.Bounds
