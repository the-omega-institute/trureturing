/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/TailLinearCoefficients
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not - specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convolution estimates and derivatives of the two linear upper-tail coefficients. -/
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

theorem upperTailLinear_gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
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

theorem hasDerivAt_upperTailLinearDecay (r t : ℝ) :
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
    have hp := ((ha.const_mul g(h)).const_add 1).mul (hasDerivAt_upperTailLinearDecay g(h) t)
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
  have hu' := (upperTailLinear_gap_pos hh hu).ne'
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
    mul_div_cancel_left₀ _ (upperTailLinear_gap_pos hh hu).ne']

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
      mul_pos (mul_pos (Real.exp_pos _) (upperTailLinear_gap_pos hh (by linarith))) hp⟩
  · rw [← integral_ell_mul_decay]
    refine intervalIntegral.integral_mono_on hu.le (hc.intervalIntegrable ..)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro t ht
    calc
      _ ≤ Real.exp (-(r*t)) * upperTailGap h t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (h1 t ht)
          (mul_nonneg (Real.exp_pos _).le (gap_nonneg hh ht.1))
      _ ≤ _ := gap_kernel_le hh hr ht.1

theorem upperTailLinear_ell_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-u) :=
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
    (fun t ht ↦ div_nonneg (gap_nonneg hh (sub_nonneg.mpr ht.2)) (upperTailLinear_gap_pos hh hu).le)
    (fun t ht ↦ (div_le_one (upperTailLinear_gap_pos hh hu)).2 (gap_mono hh (by linarith [ht.1])))
    (div_pos (upperTailLinear_gap_pos hh (by linarith)) (upperTailLinear_gap_pos hh hu))
  have hell := sq_pos_of_pos (upperTailLinear_ell_pos hu)
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

private theorem scaled_convolution1_cosh (h u : ℝ) :
    scaledTailConvolution1 h u = Real.exp (-(k(h) * u / 2)) *
      ∫ x in (0 : ℝ)..1, Real.cosh (k(h) * u * (x - 1 / 2)) *
        (upperTailGap h (u * x) / u) * (upperTailGap h (u * (1 - x)) / u) := by
  let W (x : ℝ) := (upperTailGap h (u * x) / u) * (upperTailGap h (u * (1 - x)) / u)
  let f (x : ℝ) := Real.exp (-(k(h) * u * x)) * W x
  have hf : Continuous f := by unfold f W upperTailGap; fun_prop
  have hf' : Continuous (fun x : ℝ ↦ f (1 - x)) := hf.comp (by fun_prop)
  have hsym : (∫ x in (0 : ℝ)..1, f (1 - x)) = ∫ x in (0 : ℝ)..1, f x := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (f := f) (a := 0) (b := 1) (1 : ℝ))
  have hW (x : ℝ) : W (1 - x) = W x := by
    unfold W
    rw [sub_sub_cancel]
    ring
  have hs (x : ℝ) :
      (f x + f (1 - x)) / 2 = Real.exp (-(k(h) * u / 2)) *
        (Real.cosh (k(h) * u * (x - 1 / 2)) *
        (upperTailGap h (u * x) / u) * (upperTailGap h (u * (1 - x)) / u)) := by
    simp only [f]
    rw [hW, Real.cosh_eq]
    dsimp only [W]
    rw [show -(k(h) * u * x) = -(k(h) * u / 2) + -(k(h) * u * (x - 1 / 2)) by ring,
      show -(k(h) * u * (1 - x)) = -(k(h) * u / 2) + k(h) * u * (x - 1 / 2) by ring,
      Real.exp_add, Real.exp_add]
    ring
  calc
    _ = ∫ x in (0 : ℝ)..1, f x := by
      unfold scaledTailConvolution1
      congr 1
      funext x
      simp only [f, W]
      ring_nf
    _ = ∫ x in (0 : ℝ)..1, (f x + f (1 - x)) / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add (hf.intervalIntegrable ..) (hf'.intervalIntegrable ..), hsym]
      ring
    _ = _ := by simp_rw [hs, intervalIntegral.integral_const_mul]

private theorem scaled_convolution1_symmetric_decay {h : ℝ} (hh : 0 < h) :
    DecayBetween (scaledTailConvolution1 h) (k(h) / 2 + h) := by
  intro s t hs hst
  refine ⟨?_, (scaled_convolution1_decay hh hs hst).2⟩
  let w (u x : ℝ) := Real.cosh (k(h) * u * (x - 1 / 2)) *
    (upperTailGap h (u * x) / u) * (upperTailGap h (u * (1 - x)) / u)
  have hC (u : ℝ) : Continuous (w u) := by unfold w upperTailGap; fun_prop
  have hbound : Real.exp (-(h * (t - s))) * (∫ x in (0 : ℝ)..1, w s x) ≤
      ∫ x in (0 : ℝ)..1, w t x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      ((continuous_const.mul (hC s)).intervalIntegrable ..) ((hC t).intervalIntegrable ..)
    intro x hx
    have hcx : Real.cosh (k(h) * s * (x - 1 / 2)) ≤
        Real.cosh (k(h) * t * (x - 1 / 2)) := by
      rw [Real.cosh_le_cosh]
      simp only [abs_mul, abs_of_pos (show 0 < k(h) by positivity), abs_of_pos hs,
        abs_of_pos (hs.trans_le hst)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst (by positivity)) (abs_nonneg _)
    have hx' : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    let f (u : ℝ) := upperTailGap h (u * x) / u
    let g (u : ℝ) := upperTailGap h (u * (1 - x)) / u
    have hf {u : ℝ} (hu : 0 < u) : 0 ≤ f u :=
      div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx.1)) hu.le
    have hg {u : ℝ} (hu : 0 < u) : 0 ≤ g u :=
      div_nonneg (gap_nonneg hh (mul_nonneg hu.le hx')) hu.le
    have hprod : Real.exp (-(h * (t - s))) * (f s * g s) ≤ f t * g t := by
      have hd := decay_mul (decay_scaled_gap hh hx.1) (decay_scaled_gap hh hx')
        (fun _ hu ↦ hf hu) (fun _ hu ↦ hg hu)
      rw [show h * x + h * (1 - x) = h by ring] at hd
      exact (hd hs hst).1
    change Real.exp (-(h * (t - s))) *
        (Real.cosh (k(h) * s * (x - 1 / 2)) * f s * g s) ≤
      Real.cosh (k(h) * t * (x - 1 / 2)) * f t * g t
    rw [show Real.exp (-(h * (t - s))) *
        (Real.cosh (k(h) * s * (x - 1 / 2)) * f s * g s) =
        Real.cosh (k(h) * s * (x - 1 / 2)) * (Real.exp (-(h * (t - s))) * (f s * g s)) by ring]
    calc
      _ ≤ Real.cosh (k(h) * t * (x - 1 / 2)) * (f t * g t) :=
        mul_le_mul hcx hprod (mul_nonneg (Real.exp_pos _).le (mul_nonneg (hf hs) (hg hs)))
          (Real.cosh_pos _).le
      _ = _ := (mul_assoc ..).symm
  rw [scaled_convolution1_cosh h s, scaled_convolution1_cosh h t]
  change Real.exp (-((k(h) / 2 + h) * (t - s))) *
    (Real.exp (-(k(h) * s / 2)) * (∫ x in (0 : ℝ)..1, w s x)) ≤
    Real.exp (-(k(h) * t / 2)) * (∫ x in (0 : ℝ)..1, w t x)
  rw [← mul_assoc, ← Real.exp_add,
    show -((k(h) / 2 + h) * (t - s)) + -(k(h) * s / 2) =
      -(k(h) * t / 2) + -(h * (t - s)) by ring, Real.exp_add, mul_assoc]
  exact mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

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
  field_simp [hu.ne', (upperTailLinear_ell_pos hu).ne']

private theorem P1_scaled {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    upperTailLinearP1 h u =
      g(h)*k(h)*m(h) * scaledTailConvolution1 h u /
      ((upperTailGap 1 u / u)^2 * (upperTailGap h u / u)) := by
  have he : upperTailGap 1 u = 1 - Real.exp (-u) := by simp [upperTailGap]
  rw [upperTailLinearP1, scaled_convolution1_eq hu, ← mul_div_assoc,
    ← upperTailLinearA1_convolution hh hu, he]
  field_simp [hu.ne', (upperTailLinear_ell_pos hu).ne', (upperTailLinear_gap_pos hh hu).ne']

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
    (hasDerivAt_upperTailLinearDecay q u).mul hP.hasDerivAt
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

theorem upperTailLinearP0_differentiableAt {h u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (upperTailLinearP0 h) u := by
  have hne : (1 - Real.exp (-u))^2 ≠ 0 := pow_ne_zero _ (upperTailLinear_ell_pos hu).ne'
  unfold upperTailLinearP0 upperTailLinearA upperTailGap
  fun_prop (disch := assumption)

theorem upperTailLinearP1_differentiableAt {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    DifferentiableAt ℝ (upperTailLinearP1 h) u := by
  have hne : (1 - Real.exp (-u))^2 ≠ 0 := pow_ne_zero _ (upperTailLinear_ell_pos hu).ne'
  have hg : (1 - Real.exp (-(h*u))) / h ≠ 0 := (upperTailLinear_gap_pos hh hu).ne'
  unfold upperTailLinearP1 upperTailLinearA1 upperTailGap
  fun_prop (disch := assumption)

/-- The two normalized positive coefficients have uniform relative derivative bounds. -/
theorem upperTailLinear_deriv_bounds {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    |deriv (upperTailLinearP0 h) u| ≤ k(h) * upperTailLinearP0 h u ∧
    |deriv (upperTailLinearP1 h) u| ≤ m(h) * upperTailLinearP1 h u := by
  have hpos (t : ℝ) (ht : 0 < t) := upperTailLinear_value_bounds hh ht
  have hd (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 < t) : 0 < upperTailGap r t / t :=
    div_pos (upperTailLinear_gap_pos hr ht) ht
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

/-- Symmetry of the convolution improves the lower logarithmic derivative
of the unnormalized positive linear term near the collision. -/
theorem upperTailLinearA1_deriv_ge {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    (2 / u - (k(h) / 2 + h)) * upperTailLinearA1 h u ≤ deriv (upperTailLinearA1 h) u := by
  let A := upperTailLinearA1 h
  let F (t : ℝ) := A t / t ^ 2
  let g₀ (t : ℝ) := upperTailGap h t / t
  let C := g(h) * k(h) * m(h)
  have hA : DifferentiableAt ℝ A u := by
    have hne : (1 - Real.exp (-(h*u))) / h ≠ 0 := (upperTailLinear_gap_pos hh hu).ne'
    unfold A upperTailLinearA1 upperTailGap
    fun_prop (disch := assumption)
  have hF : HasDerivAt F ((deriv A u - (2/u) * A u) / u ^ 2) u := by
    apply (hA.hasDerivAt.div (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu.ne')).congr_deriv
    field_simp [hu.ne'] <;> ring
  have hF_eq (t : ℝ) (ht : 0 < t) :
      F t = C * scaledTailConvolution1 h t / g₀ t := by
    unfold F A C g₀
    rw [scaled_convolution1_eq ht, ← mul_div_assoc, ← upperTailLinearA1_convolution hh ht]
    field_simp [ht.ne', (upperTailLinear_gap_pos hh ht).ne'] <;> ring
  have hF₀ (t : ℝ) (ht : 0 < t) : 0 ≤ F t := by
    have h := (upperTailLinear_value_bounds hh ht).2.1
    unfold upperTailLinearP1 at h
    have hAt := (div_pos_iff_of_pos_right (sq_pos_of_pos (upperTailLinear_ell_pos ht))).1 h
    exact div_nonneg hAt.le (sq_nonneg _)
  have hderiv := (deriv_from_comparison hu hF.differentiableAt
    (quotient_comparison
      (decay_const_mul (scaled_convolution1_symmetric_decay hh) (by positivity : 0 ≤ C))
      (decay_gap_quotient hh) (fun t ht ↦ div_pos (upperTailLinear_gap_pos hh ht) ht) hF₀ hF_eq)).1
  rw [hF.deriv] at hderiv
  change -((k(h) / 2 + h) * (A u / u ^ 2)) ≤ (deriv A u - (2/u) * A u) / u ^ 2 at hderiv
  rw [← mul_div_assoc, ← neg_div] at hderiv
  have h := (div_le_div_iff_of_pos_right (sq_pos_of_pos hu)).1 hderiv
  linarith only [h]

/-- At a physical degree the geometric sum gives a positive ordinary
derivative of the unnormalized linear coefficient. -/
theorem upperTailLinearA1_deriv_nonneg {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    0 ≤ deriv (upperTailLinearA1 (3 / (p : ℝ))) u := by
  let h : ℝ := 3 / (p : ℝ)
  let a := upperTailGap h
  let z := Real.exp (h * u)
  let Z := ∑ i ∈ Finset.range (p + 2), z ^ i
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have ha := upperTailLinear_gap_pos hh hu
  have hz : 0 < z - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh hu))
  have hk : k(h) = ((p + 2 : ℕ) : ℝ) * h := by
    dsimp only [h]
    push_cast
    field_simp [hpR.ne']
    <;> ring
  have hg : g(h) = ((p + 1 : ℕ) : ℝ) * h := by
    push_cast at hk ⊢
    linarith only [hk]
  have hgeom : Z * (z - 1) = Real.exp (k(h) * u) - 1 := by
    have H := geom_sum_mul_neg z (p + 2)
    have he : z ^ (p + 2) = Real.exp (k(h) * u) := by
      dsimp only [z]
      rw [← Real.exp_nat_mul, hk]
      congr 1
      ring
    rw [he] at H
    change _ = _ at H
    dsimp only [Z]
    linear_combination -H
  have hZ : ((p + 2 : ℕ) : ℝ) + h*u*(((p+2 : ℕ) : ℝ)*(p+1)/2) ≤ Z := by
    have H : (∑ i ∈ Finset.range (p+2), (1 + h*u*(i : ℝ))) ≤ Z := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Real.add_one_le_exp (h*u*(i : ℝ))
      dsimp only [z]
      rw [← Real.exp_nat_mul]
      convert hi using 1 <;> ring
    have hsum : (∑ i ∈ Finset.range (p+2), (i : ℝ)) =
        (((p+2 : ℕ) : ℝ)*(p+1))/2 := by
      have HN : (∑ i ∈ Finset.range (p+2), i) * 2 = (p+2)*(p+1) := by
        simpa only [show p + 2 - 1 = p + 1 by omega] using
          Finset.sum_range_id_mul_two (p+2)
      have HR := congrArg (fun n : ℕ ↦ (n : ℝ)) HN
      push_cast at HR ⊢
      linarith only [HR]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at H
    simpa using H
  have hL : upperTailSlope h u * (Real.exp (k(h) * u) - 1) = h * Z := by
    rw [← hgeom]
    change h / (z - 1) * (Z * (z - 1)) = h * Z
    field_simp [hz.ne']
  have hmono : 0 ≤ 2 * (h * Z) - k(h) * (g(h) * a u + 2) := by
    have hlowest := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 2*h by positivity)
    have hkg := mul_le_mul_of_nonneg_left (upperTailGap_le (t := u) hh)
      (show 0 ≤ k(h)*g(h) by positivity)
    change k(h)*g(h)*a u ≤ k(h)*g(h)*u at hkg
    rw [hk, hg] at hkg ⊢
    push_cast at hlowest hkg ⊢
    nlinarith only [hlowest, hkg]
  let e := Real.exp (-(k(h) * u))
  have hE : e * Real.exp (k(h) * u) = 1 := by
    dsimp only [e]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hA : HasDerivAt (upperTailLinearA1 h)
      (e / a u * (2 * (h * Z) - k(h) * (g(h) * a u + 2))) u := by
    have hG := hasDerivAt_upperTailGap (t := u) hh
    have hEt := hasDerivAt_upperTailLinearDecay k(h) u
    have hE1 := hEt.const_sub 1
    have hraw := ((hEt.sub_const 1).const_mul g(h)).add
      (((hE1.div hG ha.ne').const_sub k(h)).const_mul 2)
    unfold upperTailLinearA1
    apply hraw.congr_deriv
    have hLg : Real.exp (-(h*u)) = upperTailSlope h u * a u :=
      ((div_eq_iff ha.ne').1 (by rw [← hG.deriv, upperTailGap_logDeriv hh hu]))
    rw [hLg, ← hL]
    change g(h) * (-k(h) * e) +
        2 * (-((-(-k(h) * e) * a u - (1 - e) * (upperTailSlope h u * a u)) / a u ^ 2)) =
      e / a u * (2 * (upperTailSlope h u * (Real.exp (k(h) * u) - 1)) -
        k(h) * (g(h) * a u + 2))
    have hEe : e * (Real.exp (k(h) * u) - 1) = 1 - e := by linarith only [hE]
    rw [div_mul_eq_mul_div, show e *
        (2 * (upperTailSlope h u * (Real.exp (k(h) * u) - 1)) -
          k(h) * (g(h) * a u + 2)) =
        2 * upperTailSlope h u * (e * (Real.exp (k(h) * u) - 1)) -
          e * k(h) * (g(h) * a u + 2) by ring, hEe]
    have ha' : a u ≠ 0 := ha.ne'
    field_simp [ha'] <;> ring
  rw [hA.deriv]
  exact mul_nonneg (div_nonneg (Real.exp_pos _).le ha.le) hmono

#print axioms one_sub_upperTailLinearA_eq_integral
#print axioms upperTailLinearA1_eq_integral
#print axioms upperTailLinear_value_bounds
#print axioms upperTailLinear_deriv_bounds

end RefinedBMV.PositiveCenter
