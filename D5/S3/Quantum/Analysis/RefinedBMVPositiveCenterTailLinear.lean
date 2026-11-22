/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailLinear
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not - specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive convolutions and derivative bounds for the upper-tail linear remainder. -/
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterUpperTail
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

/-! # Linear error in the positive-center upper tail of the refined BMV kernel -/

open Filter MeasureTheory Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

local notation "g(" h ")" => (3 + h)
local notation "k(" h ")" => (3 + 2 * h)
local notation "m(" h ")" => (3 + 3 * h)
local notation "j(" h ")" => (1 + h)
local notation "c(" h ")" => (g(h) * k(h) / 2)

private theorem gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailGap h t :=
  div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))) hh

private theorem gap_nonneg {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    0 ≤ upperTailGap h t :=
  div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le ht)))) hh.le

private theorem gap_mono {h s t : ℝ} (hh : 0 < h) (hst : s ≤ t) :
    upperTailGap h s ≤ upperTailGap h t := by
  unfold upperTailGap
  exact div_le_div_of_nonneg_right
    (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hst hh.le))) _)
    hh.le

private theorem continuous_gap (h : ℝ) : Continuous (upperTailGap h) := by
  unfold upperTailGap
  fun_prop

attribute [local fun_prop] continuous_gap

private theorem integral_gap {r : ℝ} (hr : 0 < r) (u : ℝ) :
    (∫ t in (0 : ℝ)..u, Real.exp (-(r * t))) = upperTailGap r u := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ _ ↦ hasDerivAt_upperTailGap hr)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [upperTailGap]

private theorem hasDerivAt_decay (r t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-(r * s))) (-r * Real.exp (-(r * t))) t := by
  have hm : HasDerivAt (fun s : ℝ ↦ r * s) r t := by
    simpa using (hasDerivAt_id' t).const_mul r
  have hn : HasDerivAt (fun s : ℝ ↦ -(r * s)) (-r) t := hm.neg
  simpa only [mul_comm] using hn.exp

/-- The marginal term in the numerator of the positive-center upper-tail kernel. -/
noncomputable def upperTailLinearA (h u : ℝ) : ℝ :=
  (1 + g(h) * upperTailGap h u) * Real.exp (-(g(h) * u))

/-- The coefficient of the first power of the gap in the regularized numerator. -/
noncomputable def upperTailLinearA1 (h u : ℝ) : ℝ :=
  g(h) * (Real.exp (-(k(h) * u)) - 1) +
    2 * (k(h) - (1 - Real.exp (-(k(h) * u))) / upperTailGap h u)

/-- The normalized magnitude of the constant term in the linear remainder. -/
noncomputable def upperTailLinearP0 (h u : ℝ) : ℝ :=
  (1 - upperTailLinearA h u) / (1 - Real.exp (-u)) ^ 2

/-- The normalized coefficient of the gap in the linear remainder. -/
noncomputable def upperTailLinearP1 (h u : ℝ) : ℝ :=
  upperTailLinearA1 h u / (1 - Real.exp (-u)) ^ 2

/-- Positive convolution for the deficit of the marginal term. -/
theorem one_sub_upperTailLinearA_eq_integral {h : ℝ} (hh : 0 < h) (u : ℝ) :
    1 - upperTailLinearA h u =
      g(h) * k(h) * ∫ t in (0 : ℝ)..u, Real.exp (-(g(h) * t)) * upperTailGap h t := by
  have derivative (t : ℝ) : HasDerivAt (fun s ↦ 1 - upperTailLinearA h s)
      (g(h) * k(h) * (Real.exp (-(g(h) * t)) * upperTailGap h t)) t := by
    have ha := hasDerivAt_upperTailGap (h := h) (t := t) hh
    have hp := ((ha.const_mul g(h)).const_add 1).mul (hasDerivAt_decay g(h) t)
    have hd := (hasDerivAt_const t (1 : ℝ)).sub hp
    convert hd using 1
    · rfl
    · unfold upperTailGap
      field_simp [hh.ne']
      ring
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ derivative t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [upperTailLinearA, upperTailGap]

private theorem exp_decay_add (p q t : ℝ) :
    Real.exp (-(p * t)) * Real.exp (-(q * t)) = Real.exp (-((p + q) * t)) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem upperTailLinearA1_convolution {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    upperTailGap h u * upperTailLinearA1 h u =
      g(h) * k(h) * m(h) *
        ∫ t in (0 : ℝ)..u, Real.exp (-(k(h) * t)) * upperTailGap h t * upperTailGap h (u - t) := by
  let e := Real.exp (-(h * u))
  have hg : (0 : ℝ) < g(h) := by positivity
  have hk : (0 : ℝ) < k(h) := by positivity
  have hm : (0 : ℝ) < m(h) := by positivity
  have he (t : ℝ) : Real.exp (-(k(h) * t)) * upperTailGap h t * upperTailGap h (u - t) =
      ((1 + e) * Real.exp (-(k(h) * t)) -
        Real.exp (-(m(h) * t)) - e * Real.exp (-(g(h) * t))) / h ^ 2 := by
    have he₀ : Real.exp (-(h * t)) * Real.exp (-(h * (u - t))) = e := by
      dsimp [e]
      rw [← Real.exp_add]
      congr 1
      ring
    have he₁ : Real.exp (-(k(h) * t)) * Real.exp (-(h * (u - t))) =
        e * Real.exp (-(g(h) * t)) := by
      dsimp [e]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have he₂ : Real.exp (-(k(h) * t)) * Real.exp (-(h * t)) =
        Real.exp (-(m(h) * t)) := by
      rw [exp_decay_add]
      congr 2
      ring
    unfold upperTailGap
    calc
      _ = (Real.exp (-(k(h) * t)) -
          Real.exp (-(k(h) * t)) * Real.exp (-(h * t)) -
          Real.exp (-(k(h) * t)) * Real.exp (-(h * (u - t))) +
          Real.exp (-(k(h) * t)) * (Real.exp (-(h * t)) * Real.exp (-(h * (u - t))))) /
          h ^ 2 := by ring
      _ = _ := by rw [he₀, he₁, he₂]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_gap hk, integral_gap hg, integral_gap hm]
  have hu' := (gap_pos hh hu).ne'
  have hem : e * Real.exp (-(k(h) * u)) = Real.exp (-(m(h) * u)) := by
    dsimp [e]
    rw [exp_decay_add]
    congr 2
    ring
  have hek : e * Real.exp (-(g(h) * u)) = Real.exp (-(k(h) * u)) := by
    dsimp [e]
    rw [exp_decay_add]
    congr 2
    ring
  unfold upperTailLinearA1
  calc
    _ = upperTailGap h u * (g(h) * (Real.exp (-(k(h) * u)) - 1) + 2 * k(h)) -
        2 * (1 - Real.exp (-(k(h) * u))) := by field_simp [hu']; ring
    _ = _ := by
      unfold upperTailGap
      rw [← hem, ← hek]
      change ((1 - e) / h) * _ - _ = _
      field_simp [hh.ne', hg.ne', hk.ne', hm.ne']
      ring

/-- Positive convolution for the coefficient of the regularized linear term. -/
theorem upperTailLinearA1_eq_integral {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    upperTailLinearA1 h u =
      g(h) * k(h) * m(h) *
        ∫ t in (0 : ℝ)..u, Real.exp (-(k(h) * t)) * upperTailGap h t *
          (upperTailGap h (u - t) / upperTailGap h u) := by
  have he : (∫ t in (0 : ℝ)..u, Real.exp (-(k(h) * t)) * upperTailGap h t *
          (upperTailGap h (u - t) / upperTailGap h u)) =
      (∫ t in (0 : ℝ)..u, Real.exp (-(k(h) * t)) * upperTailGap h t *
          upperTailGap h (u - t)) / upperTailGap h u := by
    rw [← intervalIntegral.integral_div]
    simp only [mul_div_assoc]
  rw [he, ← mul_div_assoc, ← upperTailLinearA1_convolution hh hu,
    mul_div_cancel_left₀ _ (gap_pos hh hu).ne']

private theorem integral_ell_mul_decay (u : ℝ) :
    (∫ t in (0 : ℝ)..u, (1 - Real.exp (-t)) * Real.exp (-t)) =
      (1 - Real.exp (-u)) ^ 2 / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ ↦ (1 - Real.exp (-x)) ^ 2 / 2)
      ((1 - Real.exp (-t)) * Real.exp (-t)) t := by
    have hs : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-x)) (Real.exp (-t)) t := by
      have he : (fun x : ℝ ↦ 1 - Real.exp (-x)) = upperTailGap 1 := by
        funext x
        simp [upperTailGap]
      rw [he]
      simpa only [one_mul] using
        (hasDerivAt_upperTailGap (h := 1) (t := t) (by norm_num))
    convert (hs.pow 2).div_const 2 using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp

private theorem gap_kernel_le {h r t : ℝ} (hh : 0 < h) (hr : 2 ≤ r) (ht : 0 ≤ t) :
    Real.exp (-(r * t)) * upperTailGap h t ≤ (1 - Real.exp (-t)) * Real.exp (-t) := by
  calc
    _ ≤ Real.exp (-(2*t)) * t :=
      mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hr ht)))
        (upperTailGap_le hh) (gap_nonneg hh ht) (Real.exp_pos _).le
    _ ≤ Real.exp (-(2*t)) * (Real.exp t - 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
    _ = _ := by
      have h : Real.exp (-(2*t)) = Real.exp (-t) * Real.exp (-t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h, Real.exp_neg]
      field_simp [(Real.exp_pos t).ne']

private theorem weighted_gap_integral_bounds {h r u : ℝ} (hh : 0 < h) (hr : 2 ≤ r)
    (hu : 0 < u) {w : ℝ → ℝ} (hw : Continuous w)
    (h0 : ∀ t ∈ Icc 0 u, 0 ≤ w t) (h1 : ∀ t ∈ Icc 0 u, w t ≤ 1)
    (hp : 0 < w (u / 2)) :
    0 < (∫ t in (0 : ℝ)..u, Real.exp (-(r*t)) * upperTailGap h t * w t) ∧
      (∫ t in (0 : ℝ)..u, Real.exp (-(r*t)) * upperTailGap h t * w t) ≤
        (1 - Real.exp (-u))^2 / 2 := by
  have hc : Continuous (fun t ↦ Real.exp (-(r*t)) * upperTailGap h t * w t) := by fun_prop
  refine ⟨intervalIntegral.integral_pos hu hc.continuousOn ?_ ?_, ?_⟩
  · intro t ht
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (gap_nonneg hh ht.1.le))
      (h0 t (Ioc_subset_Icc_self ht))
  · exact ⟨u / 2, ⟨by linarith, by linarith⟩,
      mul_pos (mul_pos (Real.exp_pos _) (gap_pos hh (by linarith))) hp⟩
  · rw [← integral_ell_mul_decay]
    refine intervalIntegral.integral_mono_on hu.le (hc.intervalIntegrable ..)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro t ht
    calc
      _ ≤ Real.exp (-(r*t)) * upperTailGap h t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (h1 t ht)
          (mul_nonneg (Real.exp_pos _).le (gap_nonneg hh ht.1))
      _ ≤ _ := gap_kernel_le hh hr ht.1

private theorem ell_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-u) :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))

/-- Uniform value bounds for the two actual normalized coefficients. -/
theorem upperTailLinear_value_bounds {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    (0 < upperTailLinearP0 h u ∧ upperTailLinearP0 h u ≤ c(h)) ∧
    (0 < upperTailLinearP1 h u ∧ upperTailLinearP1 h u ≤ c(h) * m(h)) := by
  have h0 := weighted_gap_integral_bounds hh (r := g(h)) (by linarith) hu
    (w := fun _ ↦ 1) continuous_const (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one] at h0
  have hf : Continuous (fun t ↦ upperTailGap h (u-t) / upperTailGap h u) := by fun_prop
  have h1 := weighted_gap_integral_bounds hh (r := k(h)) (by linarith) hu hf
    (fun t ht ↦ div_nonneg (gap_nonneg hh (sub_nonneg.mpr ht.2)) (gap_pos hh hu).le)
    (fun t ht ↦ (div_le_one (gap_pos hh hu)).2 (gap_mono hh (by linarith [ht.1])))
    (div_pos (gap_pos hh (by linarith)) (gap_pos hh hu))
  have hell := sq_pos_of_pos (ell_pos hu)
  have hgk : 0 < g(h) * k(h) := by positivity
  have hgkm : 0 < g(h) * k(h) * m(h) := by positivity
  unfold upperTailLinearP0 upperTailLinearP1
  rw [one_sub_upperTailLinearA_eq_integral hh, upperTailLinearA1_eq_integral hh hu]
  refine ⟨⟨div_pos (mul_pos hgk h0.1) hell, (div_le_iff₀ hell).2 ?_⟩,
    ⟨div_pos (mul_pos hgkm h1.1) hell, (div_le_iff₀ hell).2 ?_⟩⟩
  · convert mul_le_mul_of_nonneg_left h0.2 hgk.le using 1
    ring
  · convert mul_le_mul_of_nonneg_left h1.2 hgkm.le using 1
    ring

/-- A positive integral on a fixed interval is trapped between its value at the
earlier parameter and that value times an exponential. -/
private def DecayBetween (f : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ ⦃s t : ℝ⦄, 0 < s → s ≤ t →
    Real.exp (-(r * (t - s))) * f s ≤ f t ∧ f t ≤ f s

private theorem decay_mul {f q : ℝ → ℝ} {r b : ℝ}
    (hf : DecayBetween f r) (hq : DecayBetween q b)
    (hf₀ : ∀ s > 0, 0 ≤ f s) (hq₀ : ∀ s > 0, 0 ≤ q s) :
    DecayBetween (fun s ↦ f s * q s) (r+b) := by
  intro s t hs hst
  have hleft := mul_le_mul (hf hs hst).1 (hq hs hst).1
    (mul_nonneg (Real.exp_pos _).le (hq₀ s hs)) (hf₀ t (hs.trans_le hst))
  have hprod : Real.exp (-((r+b)*(t - s))) * (f s * q s) =
      (Real.exp (-(r * (t - s))) * f s) * (Real.exp (-(b * (t - s))) * q s) := by
    rw [← exp_decay_add]
    ring
  exact ⟨hprod.trans_le hleft, mul_le_mul (hf hs hst).2 (hq hs hst).2
    (hq₀ t (hs.trans_le hst)) (hf₀ s hs)⟩

private theorem decay_exp {r : ℝ} (hr : 0 ≤ r) :
    DecayBetween (fun t ↦ Real.exp (-(r*t))) r := by
  intro s t hs hst
  rw [← Real.exp_add, show -(r * (t - s)) + -(r*s) = -(r*t) by ring]
  exact ⟨le_rfl, Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hst hr))⟩

private theorem decay_integral {F : ℝ → ℝ → ℝ} {b r : ℝ} (hb : 0 ≤ b)
    (hcont : ∀ u, Continuous (F u)) (hpos : ∀ u > 0, ∀ x ∈ Icc 0 b, 0 ≤ F u x)
    (hdecay : ∀ x ∈ Icc 0 b, ∃ q ≤ r, DecayBetween (fun u ↦ F u x) q) :
    DecayBetween (fun u ↦ ∫ x in (0 : ℝ)..b, F u x) r := by
  intro s t hs hst
  refine ⟨?_, intervalIntegral.integral_mono_on hb ((hcont t).intervalIntegrable ..)
      ((hcont s).intervalIntegrable ..) (fun x hx ↦ ?_)⟩
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hb
      ((continuous_const.mul (hcont s)).intervalIntegrable ..)
      ((hcont t).intervalIntegrable ..) (fun x hx ↦ ?_)
    obtain ⟨q, hqr, hq⟩ := hdecay x hx
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hqr (sub_nonneg.mpr hst))))
      (hpos s hs x hx)).trans (hq hs hst).1
  · obtain ⟨q, _, hq⟩ := hdecay x hx
    exact (hq hs hst).2

private theorem scaled_gap_eq_integral {r u : ℝ} (hr : 0 < r) (hu : 0 < u) (x : ℝ) :
    upperTailGap r (u*x) / u = ∫ y in (0 : ℝ)..x, Real.exp (-(r * (u*y))) := by
  apply (div_eq_iff hu.ne').2
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (f := fun y : ℝ ↦ Real.exp (-(r*y))) (a := 0) (b := x) u
  rw [mul_zero, integral_gap hr] at hs
  simpa only [smul_eq_mul, mul_comm u] using hs.symm

private theorem decay_scaled_gap {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    DecayBetween (fun u ↦ upperTailGap r (u*x) / u) (r*x) := by
  intro s t hs hst
  dsimp only
  rw [scaled_gap_eq_integral hr hs, scaled_gap_eq_integral hr (hs.trans_le hst)]
  have h : DecayBetween (fun u ↦ ∫ y in (0 : ℝ)..x, Real.exp (-(r * (u*y)))) (r*x) := by
    apply decay_integral hx (fun u ↦ by fun_prop) (fun _ _ _ _ ↦ (Real.exp_pos _).le)
    intro y hy
    refine ⟨r*y, mul_le_mul_of_nonneg_left hy.2 hr.le, ?_⟩
    simpa only [mul_assoc, mul_comm y] using decay_exp (mul_nonneg hr.le hy.1)
  exact h hs hst

private noncomputable def scaledTailConvolution0 (h u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (-(g(h)*(u*x))) * (upperTailGap h (u*x) / u)

private noncomputable def scaledTailConvolution1 (h u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (-(k(h)*(u*x))) *
    (upperTailGap h (u*x) / u) * (upperTailGap h (u*(1-x)) / u)

private theorem scaled_convolution0_decay {h : ℝ} (hh : 0 < h) :
    DecayBetween (scaledTailConvolution0 h) k(h) := by
  unfold scaledTailConvolution0
  apply decay_integral zero_le_one (fun _ ↦ by fun_prop)
  · intro u hu x hx
    exact mul_nonneg (Real.exp_pos _).le
      (div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx.1)) hu.le)
  · intro x hx
    refine ⟨g(h)*x + h*x, ?_, ?_⟩
    · have hk : 0 ≤ k(h) := by positivity
      rw [show g(h)*x + h*x = k(h)*x by ring]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2 hk
    · have he : DecayBetween (fun u ↦ Real.exp (-(g(h)*(u*x)))) (g(h)*x) := by
        simpa only [mul_assoc, mul_comm x] using
          (decay_exp (show 0 ≤ g(h)*x from mul_nonneg (by positivity) hx.1))
      exact decay_mul he (decay_scaled_gap hh hx.1) (fun _ _ ↦ (Real.exp_pos _).le)
        (fun u hu ↦ div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx.1)) hu.le)

private theorem scaled_convolution1_decay {h : ℝ} (hh : 0 < h) :
    DecayBetween (scaledTailConvolution1 h) m(h) := by
  unfold scaledTailConvolution1
  apply decay_integral zero_le_one (fun _ ↦ by fun_prop)
  · intro u hu x hx
    have hleft := div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx.1)) hu.le
    have hright := div_nonneg (gap_nonneg hh (mul_nonneg hu.le (sub_nonneg.mpr hx.2))) hu.le
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hleft) hright
  · intro x hx
    have hx' : 0 ≤ 1-x := sub_nonneg.mpr hx.2
    refine ⟨k(h)*x + h*x + h*(1-x), ?_, ?_⟩
    · have hk : 0 ≤ k(h) := by positivity
      have hle := mul_le_mul_of_nonneg_left hx.2 hk
      linarith only [hle, show h*x + h*(1-x) = h by ring]
    · have he : DecayBetween (fun u ↦ Real.exp (-(k(h)*(u*x)))) (k(h)*x) := by
        simpa only [mul_assoc, mul_comm x] using
          (decay_exp (show 0 ≤ k(h)*x from mul_nonneg (by positivity) hx.1))
      have hleft (u : ℝ) (hu : 0 < u) :=
        div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx.1)) hu.le
      have hright (u : ℝ) (hu : 0 < u) :=
        div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx')) hu.le
      exact decay_mul (decay_mul he (decay_scaled_gap hh hx.1)
        (fun _ _ ↦ (Real.exp_pos _).le) hleft)
        (decay_scaled_gap hh hx') (fun u hu ↦ mul_nonneg (Real.exp_pos _).le (hleft u hu)) hright

private theorem scaled_convolution0_eq {h u : ℝ} (hu : 0 < u) :
    scaledTailConvolution0 h u =
      (∫ t in (0 : ℝ)..u, Real.exp (-(g(h)*t)) * upperTailGap h t) / u^2 := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (f := fun t : ℝ ↦ Real.exp (-(g(h)*t)) * upperTailGap h t) (a := 0) (b := 1) u
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  unfold scaledTailConvolution0
  simp_rw [← mul_div_assoc, intervalIntegral.integral_div]
  rw [← hs]
  field_simp [hu.ne']

private theorem scaled_convolution1_eq {h u : ℝ} (hu : 0 < u) :
    scaledTailConvolution1 h u =
      (∫ t in (0 : ℝ)..u,
        Real.exp (-(k(h)*t)) * upperTailGap h t * upperTailGap h (u-t)) / u^3 := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (f := fun t : ℝ ↦ Real.exp (-(k(h)*t)) * upperTailGap h t * upperTailGap h (u-t))
    (a := 0) (b := 1) u
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  unfold scaledTailConvolution1
  have he (x : ℝ) : Real.exp (-(k(h)*(u*x))) * (upperTailGap h (u*x)/u) *
      (upperTailGap h (u*(1-x))/u) =
      (Real.exp (-(k(h)*(u*x))) * upperTailGap h (u*x) * upperTailGap h (u-u*x))/u^2 := by
    rw [show u*(1-x) = u-u*x by ring]
    ring
  simp_rw [he, intervalIntegral.integral_div]
  rw [← hs]
  field_simp [hu.ne']

private theorem P0_scaled {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    upperTailLinearP0 h u =
      g(h)*k(h) * scaledTailConvolution0 h u / (upperTailGap 1 u / u)^2 := by
  have he : upperTailGap 1 u = 1 - Real.exp (-u) := by simp [upperTailGap]
  rw [upperTailLinearP0, one_sub_upperTailLinearA_eq_integral hh, scaled_convolution0_eq hu, he]
  field_simp [hu.ne', (ell_pos hu).ne']

private theorem P1_scaled {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    upperTailLinearP1 h u =
      g(h)*k(h)*m(h) * scaledTailConvolution1 h u /
      ((upperTailGap 1 u / u)^2 * (upperTailGap h u / u)) := by
  have he : upperTailGap 1 u = 1 - Real.exp (-u) := by simp [upperTailGap]
  rw [upperTailLinearP1, scaled_convolution1_eq hu, ← mul_div_assoc,
    ← upperTailLinearA1_convolution hh hu, he]
  field_simp [hu.ne', (ell_pos hu).ne', (gap_pos hh hu).ne']

private theorem decay_const_mul {f : ℝ → ℝ} {r C : ℝ}
    (hf : DecayBetween f r) (hC : 0 ≤ C) : DecayBetween (fun t ↦ C * f t) r := by
  intro s t hs hst
  refine ⟨?_, mul_le_mul_of_nonneg_left (hf hs hst).2 hC⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hf hs hst).1 hC

private theorem decay_gap_quotient {r : ℝ} (hr : 0 < r) :
    DecayBetween (fun t ↦ upperTailGap r t / t) r := by
  simpa only [mul_one] using decay_scaled_gap hr (show (0 : ℝ) ≤ 1 by norm_num)

private theorem decay_gap_quotient_sq :
    DecayBetween (fun t ↦ (upperTailGap 1 t / t)^2) 2 := by
  have h := decay_gap_quotient (show (0 : ℝ) < 1 by norm_num)
  have hp (t : ℝ) (ht : 0 < t) : 0 ≤ upperTailGap 1 t / t :=
    div_nonneg (gap_nonneg (by norm_num) ht.le) ht.le
  convert decay_mul h h hp hp using 1
  · exact funext (fun _ ↦ pow_two _)
  · norm_num

private theorem quotient_comparison {P F G : ℝ → ℝ} {r b : ℝ}
    (hf : DecayBetween F r) (hg : DecayBetween G b) (hG : ∀ t > 0, 0 < G t)
    (hP : ∀ t > 0, 0 ≤ P t) (heq : ∀ t > 0, P t = F t / G t) :
    ∀ ⦃s t : ℝ⦄, 0 < s → s ≤ t →
      Real.exp (-(r * (t - s))) * P s ≤ P t ∧ P t ≤ Real.exp (b * (t - s)) * P s := by
  intro s t hs hst
  have ht := hs.trans_le hst
  have hs' : F s = P s * G s := (eq_div_iff (hG s hs).ne').1 (heq s hs) |>.symm
  have ht' : F t = P t * G t := (eq_div_iff (hG t ht).ne').1 (heq t ht) |>.symm
  have hf' := hf hs hst
  have hg' := hg hs hst
  rw [hs', ht'] at hf'
  constructor
  · apply le_of_mul_le_mul_right _ (hG t ht)
    calc
      _ ≤ (Real.exp (-(r * (t - s))) * P s) * G s :=
        mul_le_mul_of_nonneg_left hg'.2 (mul_nonneg (Real.exp_pos _).le (hP s hs))
      _ = Real.exp (-(r * (t - s))) * (P s * G s) := by ring
      _ ≤ _ := hf'.1
  · apply le_of_mul_le_mul_right _ (hG s hs)
    calc
      P t * G s = Real.exp (b * (t - s)) * (P t * (Real.exp (-(b * (t - s))) * G s)) := by
        rw [Real.exp_neg]
        field_simp [(Real.exp_pos (b * (t - s))).ne']
      _ ≤ Real.exp (b * (t - s)) * (P t * G t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg'.1 (hP t ht))
          (Real.exp_pos _).le
      _ ≤ Real.exp (b * (t - s)) * (P s * G s) :=
        mul_le_mul_of_nonneg_left hf'.2 (Real.exp_pos _).le
      _ = _ := by ring

private theorem deriv_from_comparison {P : ℝ → ℝ} {r b u : ℝ} (hu : 0 < u)
    (hP : DifferentiableAt ℝ P u)
    (h : ∀ ⦃s t : ℝ⦄, 0 < s → s ≤ t →
      Real.exp (-(r * (t - s))) * P s ≤ P t ∧ P t ≤ Real.exp (b * (t - s)) * P s) :
    -(r*P u) ≤ deriv P u ∧ deriv P u ≤ b*P u := by
  have hm : MonotoneOn (fun t ↦ Real.exp (-(-r*t)) * P t) (Ioi 0) := by
    intro s hs t ht hst
    have he : Real.exp (-(-r*s)) = Real.exp (-(-r*t)) * Real.exp (-(r * (t - s))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change Real.exp (-(-r*s)) * P s ≤ Real.exp (-(-r*t)) * P t
    rw [he, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h hs hst).1 (Real.exp_pos _).le
  have ha : AntitoneOn (fun t ↦ Real.exp (-(b*t)) * P t) (Ioi 0) := by
    intro s hs t ht hst
    have he : Real.exp (-(b*s)) = Real.exp (-(b*t)) * Real.exp (b * (t - s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change Real.exp (-(b*t)) * P t ≤ Real.exp (-(b*s)) * P s
    rw [he, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h hs hst).2 (Real.exp_pos _).le
  have hmu := hm.derivWithin_nonneg (x := u)
  have hau := ha.derivWithin_nonpos (x := u)
  have hderiv (q : ℝ) : HasDerivAt (fun t ↦ Real.exp (-(q*t)) * P t)
      (-q * Real.exp (-(q*u)) * P u + Real.exp (-(q*u)) * deriv P u) u :=
    (hasDerivAt_decay q u).mul hP.hasDerivAt
  have hI : UniqueDiffWithinAt ℝ (Ioi (0 : ℝ)) u := uniqueDiffOn_Ioi 0 u hu
  rw [(hderiv (-r)).hasDerivWithinAt.derivWithin hI] at hmu
  rw [(hderiv b).hasDerivWithinAt.derivWithin hI] at hau
  have hl : 0 ≤ Real.exp (-(-r*u)) * (r*P u + deriv P u) := by
    convert hmu using 1
    ring
  have hb : Real.exp (-(b*u)) * (deriv P u - b*P u) ≤ 0 := by
    convert hau using 1
    ring
  exact ⟨by linarith [nonneg_of_mul_nonneg_right hl (Real.exp_pos _)],
    sub_nonpos.mp (nonpos_of_mul_nonpos_right hb (Real.exp_pos _))⟩

private theorem upperTailLinearP0_differentiableAt {h u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (upperTailLinearP0 h) u := by
  have hne : (1 - Real.exp (-u))^2 ≠ 0 := pow_ne_zero _ (ell_pos hu).ne'
  unfold upperTailLinearP0 upperTailLinearA upperTailGap
  fun_prop (disch := assumption)

private theorem upperTailLinearP1_differentiableAt {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    DifferentiableAt ℝ (upperTailLinearP1 h) u := by
  have hne : (1 - Real.exp (-u))^2 ≠ 0 := pow_ne_zero _ (ell_pos hu).ne'
  have hg : (1 - Real.exp (-(h*u))) / h ≠ 0 := (gap_pos hh hu).ne'
  unfold upperTailLinearP1 upperTailLinearA1 upperTailGap
  fun_prop (disch := assumption)

/-- The two normalized positive coefficients have uniform relative derivative bounds. -/
theorem upperTailLinear_deriv_bounds {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    |deriv (upperTailLinearP0 h) u| ≤ k(h) * upperTailLinearP0 h u ∧
    |deriv (upperTailLinearP1 h) u| ≤ m(h) * upperTailLinearP1 h u := by
  have hpos (t : ℝ) (ht : 0 < t) := upperTailLinear_value_bounds hh ht
  have hd (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 < t) : 0 < upperTailGap r t / t :=
    div_pos (gap_pos hr ht) ht
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hsq (t : ℝ) (ht : 0 < t) : 0 < (upperTailGap 1 t / t)^2 :=
    sq_pos_of_pos (hd 1 h1 t ht)
  have h0 := deriv_from_comparison hu (upperTailLinearP0_differentiableAt hu)
    (quotient_comparison (decay_const_mul (scaled_convolution0_decay hh) (by positivity))
      decay_gap_quotient_sq hsq (fun t ht ↦ (hpos t ht).1.1.le)
      (fun _ ht ↦ P0_scaled hh ht))
  have hGap := decay_gap_quotient hh
  have hdenom := decay_mul decay_gap_quotient_sq hGap (fun t ht ↦ (hsq t ht).le)
    (fun t ht ↦ (hd h hh t ht).le)
  have h1' := deriv_from_comparison hu (upperTailLinearP1_differentiableAt hh hu)
    (quotient_comparison (decay_const_mul (scaled_convolution1_decay hh) (by positivity))
      hdenom (fun t ht ↦ mul_pos (hsq t ht) (hd h hh t ht))
      (fun t ht ↦ (hpos t ht).2.1.le) (fun _ ht ↦ P1_scaled hh ht))
  refine ⟨abs_le.2 ⟨h0.1, h0.2.trans ?_⟩, abs_le.2 ⟨h1'.1, h1'.2.trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (hpos u hu).1.1.le
  · exact mul_le_mul_of_nonneg_right (by linarith) (hpos u hu).2.1.le

/-- The linear remainder's tail multiplier with denominator power one or two. -/
noncomputable def upperTailLinearW (h : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  Real.exp (-(j(h)*d)) / upperTailGap h d ^ n

theorem hasDerivAt_upperTailLinearW {h d : ℝ} {n : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hn : n = 1 ∨ n = 2) :
    HasDerivAt (upperTailLinearW h n)
      (-(j(h) + n * upperTailSlope h d) * upperTailLinearW h n d) d := by
  have ha := gap_pos hh hd
  have ha' := upperTailGap_logDeriv hh hd
  rw [(hasDerivAt_upperTailGap hh).deriv] at ha'
  have hg : HasDerivAt (upperTailGap h) (upperTailSlope h d * upperTailGap h d) d := by
    rw [← (div_eq_iff ha.ne').1 ha']
    exact hasDerivAt_upperTailGap hh
  have he := hasDerivAt_decay j(h) d
  have hw := he.div (hg.pow n) (pow_ne_zero n ha.ne')
  unfold upperTailLinearW
  convert hw using 1
  rcases hn with rfl | rfl
  all_goals simp only [Pi.pow_apply]
  all_goals norm_num
  all_goals field_simp [ha.ne'] <;> ring

theorem hasDerivAt_deriv_upperTailLinearW {h d : ℝ} {n : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hn : n = 1 ∨ n = 2) :
    HasDerivAt (deriv (upperTailLinearW h n))
      (((j(h) + n * upperTailSlope h d)^2 +
        n * (upperTailSlope h d * (h + upperTailSlope h d))) * upperTailLinearW h n d) d := by
  have hl := (hasDerivAt_upperTailSlope hh hd).const_mul (n : ℝ) |>.const_add j(h) |>.neg
  have hw := hasDerivAt_upperTailLinearW hh hd hn
  have hprod := hl.mul hw
  have hnear : deriv (upperTailLinearW h n) =ᶠ[nhds d]
      (fun t ↦ -(j(h) + n * upperTailSlope h t) * upperTailLinearW h n t) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact (hasDerivAt_upperTailLinearW hh ht hn).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ hnear
  convert hprod using 1
  simp only [Pi.neg_apply]
  ring

/-- Uniform tail bounds for the first and second derivatives of the multipliers. -/
theorem upperTailLinearW_bounds {h d : ℝ} {n : ℕ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hd : 11 ≤ d) (hn : n = 1 ∨ n = 2) :
    let W := upperTailLinearW h n d
    0 < W ∧ W ≤ Real.exp (-d) / 3^n ∧
    |deriv (upperTailLinearW h n) d| ≤ (3/2)*W ∧
    |deriv (deriv (upperTailLinearW h n)) d| ≤ (9/4)*W := by
  dsimp only
  have hd₀ : 0 < d := by linarith
  have ha := gap_pos hh hd₀
  have ha3 := upperTailGap_ge_three hh hhmax hd
  have hW : 0 < upperTailLinearW h n d := div_pos (Real.exp_pos _) (pow_pos ha _)
  have he : Real.exp (-(j(h)*d)) ≤ Real.exp (-d) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hh.le hd₀.le]
  have hw : upperTailLinearW h n d ≤ Real.exp (-d) / 3^n :=
    div_le_div₀ (Real.exp_pos _).le he (by positivity)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) ha3 n)
  let L := upperTailSlope h d
  have hL := upperTailSlope_bounds hh hd₀
  have hL₀ : 0 < L := hL.1
  have hL₁ : L ≤ 1/11 := hL.2.1.trans ((div_le_div_iff₀ hd₀ (by norm_num)).2 (by simpa using hd))
  have hn₀ : (0 : ℝ) ≤ n := by positivity
  have hn₂ : (n : ℝ) ≤ 2 := by rcases hn with rfl | rfl <;> norm_num
  have hNL : (n : ℝ) * L ≤ 2 * (1/11) :=
    mul_le_mul hn₂ hL₁ hL₀.le (by norm_num)
  have hrate₀ : 0 ≤ j(h) + n*L := by positivity
  have hrate : j(h) + n*L ≤ 16/11 := by linarith
  have hcurv₀ : 0 ≤ L*(h+L) := by positivity
  have hcurv : L*(h+L) ≤ (1/11)*(4/11) :=
    mul_le_mul hL₁ (by linarith) (by positivity) (by norm_num)
  have hncurv : (n : ℝ) * (L*(h+L)) ≤ 2 * ((1/11)*(4/11)) :=
    mul_le_mul hn₂ hcurv hcurv₀ (by norm_num)
  have hsecond : (j(h)+n*L)^2 + n*(L*(h+L)) ≤ (9/4 : ℝ) := by
    linarith [pow_le_pow_left₀ hrate₀ hrate 2]
  refine ⟨hW, hw, ?_, ?_⟩
  · rw [(hasDerivAt_upperTailLinearW hh hd₀ hn).deriv]
    change |-(j(h) + n*L) * upperTailLinearW h n d| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg hrate₀, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_right (hrate.trans (by norm_num)) hW.le
  · rw [(hasDerivAt_deriv_upperTailLinearW hh hd₀ hn).deriv]
    change |((j(h)+n*L)^2 + n*(L*(h+L))) * upperTailLinearW h n d| ≤ _
    rw [abs_mul, abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hn₀ hcurv₀)), abs_of_pos hW]
    exact mul_le_mul_of_nonneg_right hsecond hW.le

/-- The linear summand of the normalized error, in independent coordinates u and d. -/
noncomputable def upperTailLinearError (h u d : ℝ) : ℝ :=
  (-upperTailLinearP0 h u * upperTailLinearW h 2 d +
    upperTailLinearP1 h u * upperTailLinearW h 1 d) / c(h)

/-- Recover the regularized numerator formula, including the sign of A - 1. -/
theorem upperTailLinearError_eq_regularized {h u d : ℝ} (hh : 0 < h) (hu : 0 < u)
    (hd : 0 < d) :
    upperTailLinearError h u d =
      Real.exp (-(j(h)*d)) *
        (upperTailLinearA h u - 1 + upperTailGap h d * upperTailLinearA1 h u) /
        (c(h) * upperTailGap h d ^ 2 * (1 - Real.exp (-u)) ^ 2) := by
  have hc : 0 < c(h) := by positivity
  unfold upperTailLinearError upperTailLinearP0 upperTailLinearP1 upperTailLinearW
  field_simp [hc.ne', (gap_pos hh hd).ne', (ell_pos hu).ne']
  ring

private theorem deriv_linearCombination {f g : ℝ → ℝ} {a b C x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun t ↦ (-a * f t + b * g t) / C) x =
      (-a * deriv f x + b * deriv g x) / C :=
  (((hf.hasDerivAt.const_mul (-a)).add (hg.hasDerivAt.const_mul b)).div_const C).deriv

private theorem deriv_upperTailLinearError_u {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) :
    deriv (fun t ↦ upperTailLinearError h t d) u =
      (-deriv (upperTailLinearP0 h) u * upperTailLinearW h 2 d +
        deriv (upperTailLinearP1 h) u * upperTailLinearW h 1 d) / c(h) := by
  have h0 := (upperTailLinearP0_differentiableAt (h := h) hu).hasDerivAt
  have h1 := (upperTailLinearP1_differentiableAt hh hu).hasDerivAt
  exact (((h0.neg.mul_const _).add (h1.mul_const _)).div_const _).deriv

private theorem deriv_upperTailLinearError_d {h u d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    deriv (upperTailLinearError h u) d =
      (-upperTailLinearP0 h u * deriv (upperTailLinearW h 2) d +
        upperTailLinearP1 h u * deriv (upperTailLinearW h 1) d) / c(h) :=
  deriv_linearCombination (hasDerivAt_upperTailLinearW hh hd (Or.inr rfl)).differentiableAt
    (hasDerivAt_upperTailLinearW hh hd (Or.inl rfl)).differentiableAt

/-- The two mixed partials agree by the separated product formula for the linear error. -/
theorem upperTailLinearError_mixed_commute {h u d : ℝ} (hh : 0 < h) (hu : 0 < u)
    (hd : 0 < d) :
    deriv (fun y ↦ deriv (fun x ↦ upperTailLinearError h x y) u) d =
      deriv (fun x ↦ deriv (upperTailLinearError h x) d) u := by
  simp_rw [deriv_upperTailLinearError_u hh hu, deriv_upperTailLinearError_d hh hd]
  rw [deriv_linearCombination
    (hasDerivAt_upperTailLinearW hh hd (Or.inr rfl)).differentiableAt
    (hasDerivAt_upperTailLinearW hh hd (Or.inl rfl)).differentiableAt]
  have h0 := (upperTailLinearP0_differentiableAt (h := h) hu).hasDerivAt
  have h1 := (upperTailLinearP1_differentiableAt hh hu).hasDerivAt
  exact ((((h0.neg.mul_const _).add (h1.mul_const _)).div_const _).deriv).symm

private theorem linear_absolute_bound {x₀ x₁ y₂ y₁ C m e l r : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (he : 0 ≤ e) (hl : 0 ≤ l) (_hr : 0 ≤ r)
    (hlr : l * r ≤ 6) (hm4 : m ≤ 4)
    (hx₀ : |x₀| ≤ l * C) (hx₁ : |x₁| ≤ l * (C * m))
    (hy₂ : |y₂| ≤ r * (e / 9)) (hy₁ : |y₁| ≤ r * (e / 3)) :
    |(-x₀*y₂ + x₁*y₁)/C| ≤ (26/3)*e := by
  rw [abs_div, abs_of_pos hC]
  apply (div_le_iff₀ hC).2
  have h2 := mul_le_mul hx₀ hy₂ (abs_nonneg y₂) (mul_nonneg hl hC.le)
  have h1 := mul_le_mul hx₁ hy₁ (abs_nonneg y₁) (mul_nonneg hl (mul_nonneg hC.le hm))
  calc
    _ ≤ |-x₀*y₂| + |x₁*y₁| := abs_add_le ..
    _ ≤ (l * r)*(e / 9 + m*(e / 3))*C := by
      rw [abs_mul, abs_neg, abs_mul]
      convert add_le_add h2 h1 using 1
      ring
    _ ≤ 6*(e / 9 + m*(e / 3))*C := by gcongr
    _ ≤ 6*(e / 9 + 4*(e / 3))*C := by gcongr
    _ = _ := by ring

/-- The five linear remainder terms used by the positive-center upper-tail sign
test have the same bound throughout the positive u range. -/
theorem upperTailLinearError_bounds {h u d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hu : 0 < u) (hd : 11 ≤ d) :
    let E := upperTailLinearError h
    let B := (26/3) * Real.exp (-d)
    |E u d| ≤ B ∧
    |deriv (fun x ↦ E x d) u| ≤ B ∧
    |deriv (E u) d| ≤ B ∧
    |deriv (fun y ↦ deriv (fun x ↦ E x y) u) d| ≤ B ∧
    |deriv (deriv (E u)) d| ≤ B := by
  dsimp only
  have hd₀ : 0 < d := by linarith
  have hc : 0 < c(h) := by positivity
  have hm : 0 ≤ m(h) := by positivity
  have hm4 : m(h) ≤ 4 := by linarith
  have hk4 : k(h) ≤ 4 := by linarith
  have he := (Real.exp_pos (-d)).le
  obtain ⟨⟨hp₀, hp₀'⟩, ⟨hp₁, hp₁'⟩⟩ := upperTailLinear_value_bounds hh hu
  obtain ⟨hpu₀, hpu₁⟩ := upperTailLinear_deriv_bounds hh hu
  have hp0 : |upperTailLinearP0 h u| ≤ 1*c(h) := by
    simpa only [abs_of_pos hp₀, one_mul] using hp₀'
  have hp1 : |upperTailLinearP1 h u| ≤ 1*(c(h)*m(h)) := by
    simpa only [abs_of_pos hp₁, one_mul] using hp₁'
  have hpu0 := hpu₀.trans (mul_le_mul hk4 hp₀' hp₀.le (by norm_num))
  have hpu1 := hpu₁.trans (mul_le_mul hm4 hp₁' hp₁.le (by norm_num))
  have hn1 : 1 = 1 ∨ 1 = 2 := Or.inl rfl
  have hn2 : 2 = 1 ∨ 2 = 2 := Or.inr rfl
  have hw1 := upperTailLinearW_bounds hh hhmax hd hn1
  have hw2 := upperTailLinearW_bounds hh hhmax hd hn2
  have hW1 : upperTailLinearW h 1 d ≤ Real.exp (-d)/3 := by
    simpa only [pow_one] using hw1.2.1
  have hW2 : upperTailLinearW h 2 d ≤ Real.exp (-d)/9 := by
    norm_num at hw2
    exact hw2.2.1
  have hW1₀ : |upperTailLinearW h 1 d| ≤ 1*(Real.exp (-d)/3) := by
    simpa only [abs_of_pos hw1.1, one_mul] using hW1
  have hW2₀ : |upperTailLinearW h 2 d| ≤ 1*(Real.exp (-d)/9) := by
    simpa only [abs_of_pos hw2.1, one_mul] using hW2
  have hw1' := (hasDerivAt_upperTailLinearW hh hd₀ hn1).differentiableAt
  have hw2' := (hasDerivAt_upperTailLinearW hh hd₀ hn2).differentiableAt
  have hw1'' := (hasDerivAt_deriv_upperTailLinearW hh hd₀ hn1).differentiableAt
  have hw2'' := (hasDerivAt_deriv_upperTailLinearW hh hd₀ hn2).differentiableAt
  have hw1d := hw1.2.2.1.trans (mul_le_mul_of_nonneg_left hW1 (by norm_num))
  have hw2d := hw2.2.2.1.trans (mul_le_mul_of_nonneg_left hW2 (by norm_num))
  have hw1dd := hw1.2.2.2.trans (mul_le_mul_of_nonneg_left hW1 (by norm_num))
  have hw2dd := hw2.2.2.2.trans (mul_le_mul_of_nonneg_left hW2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hW2₀ hW1₀
  · rw [deriv_upperTailLinearError_u hh hu]
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hpu0 hpu1 hW2₀ hW1₀
  · rw [deriv_upperTailLinearError_d hh hd₀]
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hw2d hw1d
  · simp_rw [deriv_upperTailLinearError_u hh hu]
    rw [deriv_linearCombination hw2' hw1']
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hpu0 hpu1 hw2d hw1d
  · have hnear : deriv (upperTailLinearError h u) =ᶠ[𝓝 d]
        (fun t ↦ (-upperTailLinearP0 h u * deriv (upperTailLinearW h 2) t +
          upperTailLinearP1 h u * deriv (upperTailLinearW h 1) t) / c(h)) := by
      filter_upwards [eventually_gt_nhds hd₀] with t ht using deriv_upperTailLinearError_d hh ht
    rw [hnear.deriv_eq, deriv_linearCombination hw2'' hw1'']
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hw2dd hw1dd

#print axioms one_sub_upperTailLinearA_eq_integral
#print axioms upperTailLinearA1_eq_integral
#print axioms upperTailLinear_value_bounds
#print axioms upperTailLinear_deriv_bounds
#print axioms hasDerivAt_upperTailLinearW
#print axioms hasDerivAt_deriv_upperTailLinearW
#print axioms upperTailLinearW_bounds
#print axioms upperTailLinearError_eq_regularized
#print axioms upperTailLinearError_mixed_commute
#print axioms upperTailLinearError_bounds

end RefinedBMV.PositiveCenter
