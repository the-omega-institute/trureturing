/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripProfile
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative weighted third derivative of the leading profile at the lower collision. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailAverage
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The leading term for a small lower coordinate and a separated upper coordinate -/

open Filter Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

private def logReciprocalGap (h t : ℝ) : ℝ := t - Real.log (upperTailGap h t)

def profileSlope (h t : ℝ) : ℝ := 1 - upperTailSlope h t

def profileCurvature (h t : ℝ) : ℝ :=
  upperTailSlope h t * (h + upperTailSlope h t)

private def geometricAngle (h a v : ℝ) : ℝ :=
  logReciprocalGap h v - logReciprocalGap h (v - a)

/-- The arithmetic-geometric mean contribution of the leading geometric factors. -/
def leftStripGeometricTerm (h a v : ℝ) : ℝ :=
  Real.cosh (geometricAngle h a v) - 1

private theorem hasDerivAt_logReciprocalGap {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (logReciprocalGap h) (profileSlope h t) t := by
  have hexp : Real.exp (-(h*t)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos (mul_pos hh ht))
  have hg : 0 < upperTailGap h t := div_pos (sub_pos.mpr hexp) hh
  have hd := hasDerivAt_upperTailGap (t := t) hh
  have hlog := hd.log hg.ne'
  have hquot := upperTailGap_logDeriv hh ht
  rw [hd.deriv] at hquot
  rw [hquot] at hlog
  exact (hasDerivAt_id' t).sub hlog

theorem hasDerivAt_profileSlope {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (profileSlope h) (profileCurvature h t) t := by
  change HasDerivAt (fun x ↦ 1 - upperTailSlope h x) (profileCurvature h t) t
  simpa only [profileCurvature, neg_neg] using (hasDerivAt_upperTailSlope hh ht).const_sub 1

theorem hasDerivAt_profileCurvature {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (profileCurvature h)
      (-(profileCurvature h t * (h + 2 * upperTailSlope h t))) t := by
  have hL := hasDerivAt_upperTailSlope hh ht
  have htProduct := hL.mul (hL.const_add h)
  change HasDerivAt (profileCurvature h) _ t at htProduct
  convert htProduct using 1 <;> unfold profileCurvature <;> ring

private theorem hasDerivAt_geometricAngle_left {h a v : ℝ} (hh : 0 < h) (hav : a < v) :
    HasDerivAt (fun x ↦ geometricAngle h x v) (profileSlope h (v-a)) a := by
  have hs := (hasDerivAt_logReciprocalGap hh (sub_pos.mpr hav)).comp a
    ((hasDerivAt_id' a).const_sub v)
  have hd := (hasDerivAt_const a (logReciprocalGap h v)).sub hs
  change HasDerivAt (fun x ↦ geometricAngle h x v) _ a at hd
  simpa only [mul_neg, mul_one, zero_sub, neg_neg] using hd

private theorem hasDerivAt_geometricAngle_right {h a v : ℝ} (hh : 0 < h) (hv : 0 < v)
    (hav : a < v) :
    HasDerivAt (geometricAngle h a) (profileSlope h v - profileSlope h (v-a)) v := by
  have hs := (hasDerivAt_logReciprocalGap hh (sub_pos.mpr hav)).comp v
    ((hasDerivAt_id' v).sub_const a)
  have hd := (hasDerivAt_logReciprocalGap hh hv).sub hs
  change HasDerivAt (geometricAngle h a) _ v at hd
  simpa only [mul_one] using hd

private theorem geometricTerm_left_second {h a v : ℝ} (hh : 0 < h) (hav : a < v) :
    deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) a =
      Real.cosh (geometricAngle h a v) * profileSlope h (v-a)^2 -
        Real.sinh (geometricAngle h a v) * profileCurvature h (v-a) := by
  have heq : (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) =ᶠ[𝓝 a]
      (fun x ↦ Real.sinh (geometricAngle h x v) * profileSlope h (v-x)) := by
    filter_upwards [eventually_lt_nhds hav] with x hx
    exact ((hasDerivAt_geometricAngle_left hh hx).cosh.sub_const 1).deriv
  have hθ := hasDerivAt_geometricAngle_left hh hav
  have hslope := (hasDerivAt_profileSlope hh (sub_pos.mpr hav)).comp a
    ((hasDerivAt_id' a).const_sub v)
  have hd := hθ.sinh.mul hslope
  change HasDerivAt (fun x ↦ Real.sinh (geometricAngle h x v) * profileSlope h (v-x)) _ a at hd
  rw [heq.deriv_eq, hd.deriv]
  simp only [Function.comp_apply, pow_two]
  ring

private theorem exp_half_le : Real.exp (1/2 : ℝ) ≤ 33/20 := by
  have hk : Real.exp (1/2 : ℝ)^2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2 : ℝ)]

private theorem sinh_half_le : Real.sinh (1/2 : ℝ) ≤ 21/40 := by
  have he := exp_half_le
  have hi : (20/33 : ℝ) ≤ (Real.exp (1/2 : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 20/33) (Real.exp_pos _)]
    exact he.trans (by norm_num)
  rw [Real.sinh_eq, Real.exp_neg]
  linarith

/-- The leading term has a uniform negative margin on the separated left strip. -/
theorem leftStrip_geometric_mixed_lt {h a v γ : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ha : 0 ≤ a) (hamax : a ≤ 1/2)
    (hgap : 6 ≤ v-a) (hγ : 5/12 ≤ γ) (hγmax : γ ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) v -
      γ * deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) a < -1/5 := by
  let s := v-a
  let θ := geometricAngle h a v
  let L := upperTailSlope h s
  let slope := profileSlope h s
  let q := profileCurvature h s
  let δ := profileSlope h v - slope
  have hs : 0 < s := by dsimp [s]; linarith
  have hv : 0 < v := by linarith
  have hav : a < v := sub_pos.mp hs
  have hsv : s ≤ v := sub_le_self _ ha
  have hLbounds (t : ℝ) (hst : s ≤ t) :
      0 < upperTailSlope h t ∧ upperTailSlope h t ≤ 1/6 ∧
        0 ≤ profileCurvature h t ∧ profileCurvature h t ≤ 1/36 := by
    have ht := hs.trans_le hst
    have ht6 : 6 ≤ t := hgap.trans hst
    obtain ⟨hl, hlt, _, hq, _, _⟩ := upperTailSlope_bounds hh ht
    rw [(hasDerivAt_upperTailSlope hh ht).deriv, neg_neg] at hq
    have hinv : 1 / t ≤ (1 : ℝ) / 6 := one_div_le_one_div_of_le (by norm_num) ht6
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 1/t) hinv 2
    have hq' : 1 / t^2 ≤ (1 : ℝ) / 36 := by
      simpa only [one_div_pow, show (1 / 6 : ℝ)^2 = 1 / 36 by norm_num] using hsquare
    refine ⟨hl, hlt.trans hinv, ?_, hq.trans hq'⟩
    unfold profileCurvature
    positivity
  have hslopebounds (t : ℝ) (hst : s ≤ t) : 5/6 ≤ profileSlope h t ∧ profileSlope h t ≤ 1 := by
    obtain ⟨hl, hlt, _⟩ := hLbounds t hst
    unfold profileSlope
    constructor <;> linarith
  obtain ⟨hL, hLmax, hq, hqmax⟩ := hLbounds s le_rfl
  obtain ⟨hslopemin, hslopemax⟩ := hslopebounds s le_rfl
  have hθ : 0 ≤ θ ∧ θ ≤ 1/2 := by
    rcases hsv.eq_or_lt with he | hlt
    · simp [θ, geometricAngle, show v-a = v from he]
    · obtain ⟨t, ht, hsec⟩ := exists_hasDerivAt_eq_slope
        (logReciprocalGap h) (profileSlope h) hlt
        (fun t ht ↦ (hasDerivAt_logReciprocalGap hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
        (fun t ht ↦ hasDerivAt_logReciprocalGap hh (hs.trans ht.1))
      have heq : profileSlope h t * (v-s) = θ := by
        exact (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp hsec
      rw [← heq]
      have hA : v - s = a := by dsimp [s]; ring
      rw [hA]
      obtain ⟨hlo, hhi⟩ := hslopebounds t ht.1.le
      constructor
      · exact mul_nonneg (by linarith) ha
      · exact (mul_le_of_le_one_left ha hhi).trans hamax
  have hδ : 0 ≤ δ ∧ δ ≤ 1/72 := by
    rcases hsv.eq_or_lt with he | hlt
    · simp [δ, slope, he]
    · obtain ⟨t, ht, hsec⟩ := exists_hasDerivAt_eq_slope
        (profileSlope h) (profileCurvature h) hlt
        (fun t ht ↦ (hasDerivAt_profileSlope hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
        (fun t ht ↦ hasDerivAt_profileSlope hh (hs.trans ht.1))
      have heq : profileCurvature h t * (v-s) = δ :=
        (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp hsec
      rw [← heq]
      have hA : v - s = a := by dsimp [s]; ring
      rw [hA]
      obtain ⟨_, _, hq, hqmax⟩ := hLbounds t ht.1.le
      refine ⟨mul_nonneg hq ha, ?_⟩
      calc
        _ ≤ (1/36 : ℝ) * (1/2) := mul_le_mul hqmax hamax ha (by norm_num)
        _ = _ := by norm_num
  have heq : (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) =ᶠ[𝓝 v]
      (fun y ↦ Real.cosh (geometricAngle h a y) * profileSlope h (y-a)^2 -
        Real.sinh (geometricAngle h a y) * profileCurvature h (y-a)) := by
    filter_upwards [eventually_gt_nhds hav] with y hy
    exact geometricTerm_left_second hh hy
  have hDθ := hasDerivAt_geometricAngle_right hh hv hav
  have hDslope := (hasDerivAt_profileSlope hh hs).comp v ((hasDerivAt_id' v).sub_const a)
  have hDq := (hasDerivAt_profileCurvature hh hs).comp v ((hasDerivAt_id' v).sub_const a)
  have hformula :
      deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) v -
        γ * deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) a =
      Real.cosh θ * (2*slope*q - δ*q - γ*slope^2) +
        Real.sinh θ * (δ*slope^2 + q*(h+2*L) + γ*q) := by
    have hd := (hDθ.cosh.mul (hDslope.pow 2)).sub (hDθ.sinh.mul hDq)
    change HasDerivAt (fun y ↦ Real.cosh (geometricAngle h a y) * profileSlope h (y-a)^2 -
        Real.sinh (geometricAngle h a y) * profileCurvature h (y-a)) _ v at hd
    rw [heq.deriv_eq, geometricTerm_left_second hh hav, hd.deriv]
    dsimp [θ, δ, slope, q, L, s]
    ring
  have hslope₀ : 0 ≤ slope := by linarith
  have hγ₀ : 0 ≤ γ := by linarith
  have hslopesq : (5/6 : ℝ)^2 ≤ slope^2 := pow_le_pow_left₀ (by norm_num) hslopemin 2
  have hslopesq' : slope^2 ≤ 1 := (pow_le_pow_left₀ hslope₀ hslopemax 2).trans_eq (by norm_num)
  have hmain : 2*slope*q - δ*q - γ*slope^2 ≤ 2/36 - (5/12)*(5/6)^2 := by
    have hm := mul_le_of_le_one_left hq hslopemax
    have hs := mul_le_mul hγ hslopesq (by positivity) hγ₀
    nlinarith only [hm, hqmax, hs, mul_nonneg hδ.1 hq]
  have hsub : δ*slope^2 + q*(h+2*L) + γ*q ≤ 1/72 + (1/36)*(3/11+1/3) + 1/36 := by
    have h1 := (mul_le_of_le_one_right hδ.1 hslopesq').trans hδ.2
    have h2 := mul_le_mul hqmax (show h+2*L ≤ 3/11+1/3 by linarith)
      (by positivity : 0 ≤ h+2*L) (by norm_num : (0 : ℝ) ≤ 1/36)
    have h3 := (mul_le_of_le_one_left hq hγmax).trans hqmax
    linarith
  have hcosh := Real.one_le_cosh θ
  have hsinh₀ : 0 ≤ Real.sinh θ := Real.sinh_nonneg_iff.mpr hθ.1
  have hsinh := (Real.sinh_le_sinh.mpr hθ.2).trans sinh_half_le
  rw [hformula]
  calc
    _ ≤ (2/36 - (5/12)*(5/6)^2) +
        (21/40)*(1/72 + (1/36)*(3/11+1/3) + 1/36) := by
      have hcosh' : Real.cosh θ * (2/36 - (5/12)*(5/6)^2) ≤ 2/36 - (5/12)*(5/6)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonpos_right hcosh
          (by norm_num : (2/36 - (5/12)*(5/6)^2 : ℝ) ≤ 0)
      have h1 := (mul_le_mul_of_nonneg_left hmain (Real.cosh_pos θ).le).trans hcosh'
      have h2 := (mul_le_mul_of_nonneg_left hsub hsinh₀).trans
        (mul_le_mul_of_nonneg_right hsinh (by norm_num))
      linarith
    _ < (-1/5 : ℝ) := by norm_num

private theorem separated_exp_neg_le {t : ℝ} (ht : 6 ≤ t) :
    Real.exp (-t) ≤ 1/400 := by
  have he6 : (400 : ℝ) < Real.exp 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    have ho : (2718/1000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    exact (by norm_num : (400 : ℝ) < (2718/1000)^6).trans
      (pow_lt_pow_left₀ ho (by norm_num) (by decide))
  have he6neg : Real.exp (-6) ≤ (1 : ℝ)/400 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he6.le
  exact (Real.exp_le_exp.mpr (neg_le_neg ht)).trans he6neg

/-- Quantitative lower bound for the marginal root at gaps of at least six. -/
theorem separated_radical_lower {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11) (ht : 6 ≤ t) :
    let B := ((3+h)*(3+2*h)/2) * (upperTailGap h t)^2 * Real.exp (-(2*t))
    B < 1/750 ∧ (999/1000 : ℝ) ≤ Real.sqrt (1 - upperTailLambda h t) := by
  let a := upperTailGap h t
  let α := 3+h
  let c := α*(3+2*h)/2
  let e := Real.exp (-t)
  have ht₀ : 0 < t := by linarith
  have he₀ : 0 < e := Real.exp_pos _
  have he : e ≤ 1/400 := separated_exp_neg_le ht
  have hte : t*e ≤ 6/400 := by
    have htExp : t ≤ 6*Real.exp (t-6) := by
      linarith only [Real.add_one_le_exp (t-6), ht]
    have hmul := mul_le_mul_of_nonneg_right htExp he₀.le
    have hexp : Real.exp (t-6)*e = Real.exp (-6) := by
      dsimp only [e]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp] at hmul
    exact hmul.trans (by linarith only [separated_exp_neg_le (t := 6) le_rfl])
  have ha₀ : 0 ≤ a := by
    refine div_nonneg (sub_nonneg.mpr ?_) hh.le
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le ht₀.le))
  have hae : a*e ≤ 6/400 :=
    (mul_le_mul_of_nonneg_right (upperTailGap_le hh) he₀.le).trans hte
  have hc : c ≤ 702/121 := by
    have h₁ : α ≤ 36/11 := by dsimp [α]; linarith only [hhmax]
    have h₂ : 3+2*h ≤ 39/11 := by linarith only [hhmax]
    have hProd := mul_le_mul h₁ h₂ (by positivity : 0 ≤ 3+2*h)
      (by norm_num : (0 : ℝ) ≤ 36/11)
    dsimp only [c]
    linarith only [hProd]
  have he2 : Real.exp (-(2*t)) = e^2 := by
    dsimp only [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hB : c*a^2*Real.exp (-(2*t)) < 1/750 := by
    have hsq := pow_le_pow_left₀ (mul_nonneg ha₀ he₀.le) hae 2
    have hcap := mul_le_mul hc hsq (sq_nonneg (a*e)) (by norm_num : (0 : ℝ) ≤ 702/121)
    rw [he2]
    exact (show c*a^2*e^2 ≤ (702/121)*(6/400)^2 by nlinarith only [hcap]).trans_lt (by norm_num)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαmax : α ≤ 36/11 := by dsimp [α]; linarith only [hhmax]
  have hexp : Real.exp (-(α*t)) ≤ e^3 := by
    rw [show e^3 = Real.exp (-(3*t)) by
      dsimp only [e]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring]
    apply Real.exp_le_exp.mpr
    dsimp [α]
    nlinarith only [mul_nonneg hh.le ht₀.le]
  have hA : (1+α*a)*Real.exp (-(α*t)) < 1/1000000 := by
    have heSq := pow_le_pow_left₀ he₀.le he 2
    have hA₀ : 0 ≤ 1+α*a := by positivity
    have hleft := mul_le_mul_of_nonneg_left hexp hA₀
    have hfirst := pow_le_pow_left₀ he₀.le he 3
    have hsecond := mul_le_mul hαmax hae (mul_nonneg ha₀ he₀.le)
      (by norm_num : (0 : ℝ) ≤ 36/11)
    have hthird := mul_le_mul hsecond heSq (sq_nonneg e)
      (by norm_num : (0 : ℝ) ≤ (36/11)*(6/400))
    nlinarith only [hleft, hfirst, hthird]
  refine ⟨hB, Real.le_sqrt_of_sq_le ?_⟩
  change (999/1000 : ℝ)^2 ≤ 1 - ((1+α*a)*Real.exp (-(α*t)) + c*a^2*Real.exp (-(2*t)))
  linarith only [hA, hB]

/-- The repeat-node correction is small relative to the leading square. -/
theorem separated_marginal_correction_lt {h t : ℝ} (hh : 0 < h) (ht : 6 ≤ t) :
    let a := upperTailGap h t
    let B := ((3+h)*(3+2*h)/2) * a^2 * Real.exp (-(2*t))
    (1+(3+h)*a)*Real.exp (-((3+h)*t)) < B/3400 := by
  let a := upperTailGap h t
  let c := (3+h)*(3+2*h)/2
  let L := upperTailSlope h t
  let e := Real.exp (-t)
  let B := c*a^2*Real.exp (-(2*t))
  let A := (1+(3+h)*a)*Real.exp (-((3+h)*t))
  have ht₀ : 0 < t := by linarith
  have ha₀ : 0 < a := div_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht₀)))) hh
  have hc : 9/2 ≤ c := by dsimp [c]; nlinarith [sq_nonneg h]
  have hc₀ : 0 < c := by linarith
  have hB : 0 < B := mul_pos (mul_pos hc₀ (sq_pos_of_pos ha₀)) (Real.exp_pos _)
  obtain ⟨hL₀, hL, _, _, _, _⟩ := upperTailSlope_bounds hh ht₀
  have hLg : L*a = Real.exp (-(h*t)) := by
    have hd := upperTailGap_logDeriv hh ht₀
    rw [(hasDerivAt_upperTailGap hh).deriv] at hd
    exact ((div_eq_iff ha₀.ne').mp hd).symm
  have hsum : a*(h+L) = 1 := by
    have hgap : h*a = 1-Real.exp (-(h*t)) := by
      change h*((1-Real.exp (-(h*t)))/h) = _
      field_simp [hh.ne']
    linarith only [hgap, hLg, show a*(h+L) = h*a+L*a by ring]
  have hCoef : L*(3+2*h) ≤ 3/t := by
    have hExp := Real.quadratic_le_exp_of_nonneg (mul_nonneg hh.le ht₀.le)
    have hden : 0 < Real.exp (h*t)-1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh ht₀))
    change (h/(Real.exp (h*t)-1))*(3+2*h) ≤ 3/t
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ hden ht₀).2
    have H : 0 ≤ h^2 * t * (3*t/2-2) :=
      mul_nonneg (mul_nonneg (sq_nonneg h) ht₀.le) (by linarith)
    nlinarith only [hExp, H]
  have hInv : 1/t ≤ (1 : ℝ)/6 := one_div_le_one_div_of_le (by norm_num) ht
  have hLmax : L ≤ 1/6 := hL.trans hInv
  have hCoeff : L*(L+3+2*h) ≤ 19/36 := by
    have hSq := pow_le_pow_left₀ hL₀.le hLmax 2
    have hRatio : 3/t ≤ (1 : ℝ)/2 := (div_le_iff₀ ht₀).2 (by linarith)
    nlinarith only [hSq, hCoef, hRatio]
  have hIdentity : c * (A/B) = e * (L*(L+3+2*h)) := by
    have he : Real.exp (-((3+h)*t)) =
        Real.exp (-(2*t))*e*Real.exp (-(h*t)) := by
      dsimp only [e]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    dsimp only [A, B]
    rw [he, ← hLg]
    field_simp [ha₀.ne', hc₀.ne', (Real.exp_pos (-(2*t))).ne']
    linear_combination -(e*L) * hsum
  have hRhs :=
    mul_le_mul_of_nonneg_left hCoeff (Real.exp_pos (-t)).le
  have hExp := mul_le_mul_of_nonneg_right (separated_exp_neg_le ht)
    (by norm_num : (0 : ℝ) ≤ 19/36)
  have hRatio : A/B < 1/3400 := by
    apply (mul_lt_mul_iff_of_pos_left hc₀).mp
    rw [hIdentity]
    linarith only [hRhs, hExp, hc]
  change A < B/3400
  exact ((div_lt_iff₀ hB).mp hRatio).trans_eq (by ring)

private def separatedSquare (h t : ℝ) : ℝ :=
  ((3 + h) * (3 + 2 * h) / 2) * (upperTailGap h t)^2 * Real.exp (-(2 * t))

private theorem hasDerivAt_separatedSquare {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (separatedSquare h) (-2 * profileSlope h t * separatedSquare h t) t := by
  have ha : 0 < upperTailGap h t := div_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))) hh
  have hs := hasDerivAt_upperTailGap (t := t) hh
  have hl := (div_eq_iff ha.ne').mp (upperTailGap_logDeriv hh ht)
  rw [hs.deriv] at hl
  have he : HasDerivAt (fun x : ℝ ↦ -(2*x)) (-2) t := by
    have hd := ((hasDerivAt_id' t).const_mul 2).neg
    change HasDerivAt (fun x : ℝ ↦ -(2*x)) _ t at hd
    simpa only [mul_one] using hd
  have hd := ((hs.pow 2).const_mul ((3+h)*(3+2*h)/2)).mul he.exp
  change HasDerivAt (separatedSquare h) _ t at hd
  apply hd.congr_deriv
  unfold separatedSquare profileSlope
  rw [hl]
  simp only [Pi.pow_apply]
  ring

/-- The first three derivatives of the leading square retain alternating signs
on the separated interval. The bounds use the actual logarithmic slope. -/
theorem separated_square_derivative_bounds {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 6 ≤ t) :
    let B : ℝ → ℝ := fun x ↦ ((3 + h) * (3 + 2 * h) / 2) *
      (upperTailGap h x)^2 * Real.exp (-(2 * x))
    0 ≤ -deriv B t ∧ -deriv B t ≤ 2 * B t ∧
      0 ≤ deriv (deriv B) t ∧ deriv (deriv B) t ≤ 4 * B t ∧
      0 ≤ -deriv (deriv (deriv B)) t ∧ -deriv (deriv (deriv B)) t ≤ 8 * B t := by
  let B := separatedSquare h
  let L := upperTailSlope h t
  let s := profileSlope h t
  let q := profileCurvature h t
  let B₂ (x : ℝ) := (4 * profileSlope h x ^ 2 - 2 * profileCurvature h x) * B x
  have ht₀ : 0 < t := by linarith
  have hB₁ (x : ℝ) (hx : 0 < x) : deriv B x = -2 * profileSlope h x * B x :=
    (hasDerivAt_separatedSquare hh hx).deriv
  have hB₂ (x : ℝ) (hx : 0 < x) : deriv (deriv B) x = B₂ x := by
    have heq : deriv B =ᶠ[𝓝 x] fun y ↦ -2 * profileSlope h y * B y := by
      filter_upwards [eventually_gt_nhds hx] with y hy using hB₁ y hy
    have hd := ((hasDerivAt_profileSlope hh hx).const_mul (-2)).mul
      (hasDerivAt_separatedSquare hh hx)
    change HasDerivAt (fun y ↦ -2 * profileSlope h y * B y) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    unfold B₂
    ring
  have hB₃ : deriv (deriv (deriv B)) t =
      (-8*s^3 + 12*s*q + 2*q*(h+2*L)) * B t := by
    have heq : deriv (deriv B) =ᶠ[𝓝 t] B₂ := by
      filter_upwards [eventually_gt_nhds ht₀] with x hx using hB₂ x hx
    have hs := (hasDerivAt_profileSlope hh ht₀).pow 2 |>.const_mul 4
    have hq := (hasDerivAt_profileCurvature hh ht₀).const_mul 2
    have hd := (hs.sub hq).mul (hasDerivAt_separatedSquare hh ht₀)
    change HasDerivAt B₂ _ t at hd
    rw [heq.deriv_eq, hd.deriv]
    dsimp only [s, q, L, B]
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  obtain ⟨hL₀, hL, hq₀, hq, _, _⟩ := upperTailSlope_bounds hh ht₀
  rw [(hasDerivAt_upperTailSlope hh ht₀).deriv, neg_neg] at hq₀ hq
  change 0 ≤ q at hq₀
  have hInv : 1/t ≤ (1 : ℝ)/6 := one_div_le_one_div_of_le (by norm_num) ht
  have hLmax : L ≤ 1 / 6 := hL.trans hInv
  have hqmax : q ≤ 1 / 36 := hq.trans (by
    simpa only [one_div_pow, show (1/6 : ℝ)^2 = 1/36 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1/t) hInv 2)
  have hs₀ : (5 / 6 : ℝ) ≤ s := by
    change (5/6 : ℝ) ≤ 1 - L
    linarith only [hLmax]
  have hs₁ : s ≤ 1 := by
    change 1 - upperTailSlope h t ≤ 1
    linarith only [hL₀]
  have hspos : 0 ≤ s := by linarith
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5/6) hs₀ 2
  have hsq' := pow_le_pow_left₀ hspos hs₁ 2
  have hcub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5/6) hs₀ 3
  have hcub' := pow_le_pow_left₀ hspos hs₁ 3
  have hsq0 : 0 ≤ 4*s^2-2*q := by nlinarith only [hsq, hqmax]
  have hsq4 : 4*s^2-2*q ≤ 4 := by nlinarith only [hsq', hq₀]
  have hqL₀ : 0 ≤ h+2*L := add_nonneg hh.le (mul_nonneg (by norm_num) hL₀.le)
  have hqL : h+2*L ≤ 3/11+1/3 := by linarith only [hhmax, hLmax]
  have hA := mul_le_mul hs₁ hqmax hq₀ (by norm_num : (0 : ℝ) ≤ 1)
  have hC := mul_le_mul hqmax hqL hqL₀ (by norm_num : (0 : ℝ) ≤ 1/36)
  have h3₀ : 0 ≤ 8*s^3-12*s*q-2*q*(h+2*L) := by
    nlinarith only [hcub, hA, hC]
  have h38 : 8*s^3-12*s*q-2*q*(h+2*L) ≤ 8 := by
    nlinarith only [hcub', mul_nonneg hspos hq₀, mul_nonneg hq₀ hqL₀]
  have hBt : 0 ≤ B t := by dsimp [B, separatedSquare]; positivity
  change 0 ≤ -deriv B t ∧ -deriv B t ≤ 2*B t ∧
    0 ≤ deriv (deriv B) t ∧ deriv (deriv B) t ≤ 4*B t ∧
    0 ≤ -deriv (deriv (deriv B)) t ∧ -deriv (deriv (deriv B)) t ≤ 8*B t
  rw [hB₃, hB₂ t ht₀, hB₁ t ht₀]
  change 0 ≤ -(-2*s*B t) ∧ -(-2*s*B t) ≤ 2*B t ∧
    0 ≤ (4*s^2-2*q)*B t ∧ (4*s^2-2*q)*B t ≤ 4*B t ∧
    0 ≤ -((-8*s^3+12*s*q+2*q*(h+2*L))*B t) ∧
    -((-8*s^3+12*s*q+2*q*(h+2*L))*B t) ≤ 8*B t
  exact ⟨by nlinarith only [mul_nonneg hspos hBt],
    by nlinarith only [mul_le_mul_of_nonneg_right hs₁ hBt],
    mul_nonneg hsq0 hBt, mul_le_mul_of_nonneg_right hsq4 hBt,
    by nlinarith only [mul_nonneg h3₀ hBt],
    by nlinarith only [mul_le_mul_of_nonneg_right h38 hBt]⟩

private def separatedCorrection (h t : ℝ) : ℝ :=
  (1 + (3 + h) * upperTailGap h t) * Real.exp (-((3 + h) * t))

/-- The first three derivatives of the separated repeat-node correction are
bounded by the corresponding powers of its exponential rate. -/
theorem separated_correction_derivative_bounds {h t : ℝ} (hh : 0 < h) (ht : 6 ≤ t) :
    let α : ℝ := 3 + h
    let A : ℝ → ℝ := fun x ↦ (1 + α * upperTailGap h x) * Real.exp (-(α*x))
    0 ≤ -deriv A t ∧ -deriv A t ≤ α * A t ∧
      0 ≤ deriv (deriv A) t ∧ deriv (deriv A) t ≤ α^2 * A t ∧
      0 ≤ -deriv (deriv (deriv A)) t ∧ -deriv (deriv (deriv A)) t ≤ α^3 * A t := by
  let α := 3+h
  let k := α*(α+h)
  let a := upperTailGap h
  let q (x : ℝ) := Real.exp (-(h*x))
  let e (x : ℝ) := Real.exp (-(α*x))
  let A := separatedCorrection h
  let D₁ (x : ℝ) := -k*a x*e x
  let D₂ (x : ℝ) := k*(α*a x-q x)*e x
  let D₃ (x : ℝ) := k*((2*α+h)*q x-α^2*a x)*e x
  have hGap (x : ℝ) : h*a x = 1-q x := by
    change h*((1-q x)/h) = _
    field_simp [hh.ne']
  have hExp (r x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp (-(r*y)))
      (-r*Real.exp (-(r*x))) x := by
    have hd := ((hasDerivAt_id' x).const_mul r).neg
    change HasDerivAt (fun y : ℝ ↦ -(r*y)) _ x at hd
    simpa only [mul_one, mul_comm] using hd.exp
  have hD₁ (x : ℝ) : HasDerivAt A (D₁ x) x := by
    have hd := (((hasDerivAt_upperTailGap (t := x) hh).const_mul α).const_add 1).mul (hExp α x)
    change HasDerivAt A _ x at hd
    apply hd.congr_deriv
    change α*q x*e x + (1+α*a x)*(-α*e x) = _
    dsimp only [D₁, k]
    linear_combination (α*e x)*(hGap x)
  have hD₂ (x : ℝ) : HasDerivAt D₁ (D₂ x) x := by
    have hd := ((hasDerivAt_upperTailGap (t := x) hh).const_mul (-k)).mul (hExp α x)
    change HasDerivAt D₁ _ x at hd
    apply hd.congr_deriv
    change -k*q x*e x + -k*a x*(-α*e x) = _
    dsimp only [D₂]
    ring
  have hD₃ (x : ℝ) : HasDerivAt D₂ (D₃ x) x := by
    have hd := ((((hasDerivAt_upperTailGap (t := x) hh).const_mul α).sub (hExp h x)).const_mul k).mul
      (hExp α x)
    change HasDerivAt D₂ _ x at hd
    apply hd.congr_deriv
    change k*(α*q x - -h*q x)*e x + k*(α*a x-q x)*(-α*e x) = _
    dsimp only [D₃]
    ring
  have hEq₁ : deriv A = D₁ := funext fun x ↦ (hD₁ x).deriv
  have hEq₂ : deriv D₁ = D₂ := funext fun x ↦ (hD₂ x).deriv
  have hEq₃ : deriv D₂ = D₃ := funext fun x ↦ (hD₃ x).deriv
  have ht₀ : 0 < t := by linarith
  have ha : 0 ≤ a t := (div_nonneg
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le ht₀.le))))
    hh.le : 0 ≤ upperTailGap h t)
  have hα : (3 : ℝ) ≤ α := by dsimp [α]; linarith only [hh]
  have hα₀ : 0 ≤ α := by linarith
  have hk : 0 ≤ k := mul_nonneg hα₀ (add_nonneg hα₀ hh.le)
  have he : 0 ≤ e t := (Real.exp_pos _).le
  have hq : 0 ≤ q t := (Real.exp_pos _).le
  have hL := (upperTailSlope_bounds hh ht₀).2.1.trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) ht)
  have ha' : 0 < a t := div_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht₀)))) hh
  have hqEq : q t = upperTailSlope h t * a t := by
    have hl := upperTailGap_logDeriv hh ht₀
    rw [(hasDerivAt_upperTailGap hh).deriv] at hl
    exact (div_eq_iff ha'.ne').mp hl
  have hqSmall : q t ≤ a t / 6 := by
    rw [hqEq, div_eq_inv_mul]
    simpa only [one_div] using mul_le_mul_of_nonneg_right hL ha
  have hFirst : (α+h)*a t ≤ 1+α*a t := by
    linarith only [hGap t, hq, show (α+h)*a t = α*a t + h*a t by ring]
  have hSecond : 0 ≤ α*a t-q t := by
    have hM := mul_le_mul_of_nonneg_right hα ha
    linarith only [hqSmall, hM, ha]
  have hThird : 0 ≤ α^2*a t-(2*α+h)*q t := by
    have hmax : 2*α+h ≤ 3*α := by dsimp [α]; linarith
    have hprod := mul_le_mul hmax hqSmall hq (by positivity : 0 ≤ 3*α)
    have hαle : α/2 ≤ α^2 := by nlinarith only [hα, mul_nonneg hα₀ (sub_nonneg.mpr hα)]
    have hAp := mul_le_mul_of_nonneg_right hαle ha
    nlinarith only [hprod, hAp]
  have hA₁ : k*a t*e t ≤ α*A t := by
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFirst hα₀) he
    change _ ≤ α*((1+α*a t)*e t)
    dsimp only [k]
    nlinarith only [hm]
  have hA₂ : D₂ t ≤ α^2*A t := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_self (α*a t) hq) hk
    have hm' := mul_le_mul_of_nonneg_right hm he
    have hm'' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFirst (sq_nonneg α)) he
    change _ ≤ α^2*((1+α*a t)*e t)
    dsimp only [D₂, k]
    nlinarith only [hm', hm'']
  have hA₃ : -D₃ t ≤ α^3*A t := by
    have htq : 0 ≤ (2*α+h)*q t := by positivity
    have hm := mul_le_mul_of_nonneg_left (sub_le_self (α^2*a t) htq) hk
    have hm' := mul_le_mul_of_nonneg_right hm he
    have hm'' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFirst (pow_nonneg hα₀ 3)) he
    change _ ≤ α^3*((1+α*a t)*e t)
    dsimp only [D₃, k]
    nlinarith only [hm', hm'']
  change 0 ≤ -deriv A t ∧ -deriv A t ≤ α*A t ∧
    0 ≤ deriv (deriv A) t ∧ deriv (deriv A) t ≤ α^2*A t ∧
    0 ≤ -deriv (deriv (deriv A)) t ∧ -deriv (deriv (deriv A)) t ≤ α^3*A t
  rw [hEq₁, hEq₂, hEq₃]
  exact ⟨by
      simp only [D₁, neg_mul, neg_neg]
      exact mul_nonneg (mul_nonneg hk ha) he,
    by simpa only [D₁, neg_mul, neg_neg] using hA₁,
    mul_nonneg (mul_nonneg hk hSecond) he, hA₂,
    by dsimp only [D₃]; nlinarith only [mul_nonneg (mul_nonneg hk hThird) he],
    hA₃⟩

/-- The square root's first three derivatives are controlled by the small
leading square throughout the separated part of the left strip. -/
theorem separated_radical_derivative_bounds {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ht : 6 ≤ t) :
    let B := ((3+h)*(3+2*h)/2) * (upperTailGap h t)^2 * Real.exp (-(2*t))
    let b : ℝ → ℝ := fun x ↦ Real.sqrt (1 - upperTailLambda h x)
    |deriv b t| ≤ (13/10)*B ∧ |deriv (deriv b) t| ≤ (33/10)*B ∧
      |deriv (deriv (deriv b)) t| ≤ (83/10)*B := by
  let A := separatedCorrection h
  let B := separatedSquare h
  let S : ℝ → ℝ := fun x ↦ 1 - upperTailLambda h x
  let b : ℝ → ℝ := fun x ↦ Real.sqrt (S x)
  have hA : ContDiff ℝ 3 A := by unfold A separatedCorrection upperTailGap; fun_prop
  have hB : ContDiff ℝ 3 B := by unfold B separatedSquare upperTailGap; fun_prop
  have hS : ContDiff ℝ 3 S := by dsimp [S, upperTailLambda, upperTailGap]; fun_prop
  have hA₁ : ContDiff ℝ 2 (deriv A) := hA.deriv'
  have hA₂ : ContDiff ℝ 1 (deriv (deriv A)) := hA₁.deriv'
  have hB₁ : ContDiff ℝ 2 (deriv B) := hB.deriv'
  have hB₂ : ContDiff ℝ 1 (deriv (deriv B)) := hB₁.deriv'
  have hS₁ : deriv S = fun x ↦ -(deriv A x + deriv B x) := by
    funext x
    change deriv (fun y ↦ 1 - (A y + B y)) x = _
    rw [deriv_const_sub, deriv_fun_add (hA.differentiable (by decide) x)
      (hB.differentiable (by decide) x)]
  have hS₂ : deriv (deriv S) = fun x ↦ -(deriv (deriv A) x + deriv (deriv B) x) := by
    funext x
    rw [hS₁, deriv.fun_neg, deriv_fun_add (hA₁.differentiable (by decide) x)
      (hB₁.differentiable (by decide) x)]
  have hS₃ : deriv (deriv (deriv S)) t =
      -(deriv (deriv (deriv A)) t + deriv (deriv (deriv B)) t) := by
    rw [hS₂, deriv.fun_neg, deriv_fun_add (hA₂.differentiable (by decide) t)
      (hB₂.differentiable (by decide) t)]
  obtain ⟨hBmax, hbmin⟩ := separated_radical_lower hh hhmax ht
  change B t < 1/750 at hBmax
  change (999/1000 : ℝ) ≤ b t at hbmin
  have hbpos : 0 < b t := by linarith
  have hSt : 0 < S t := Real.sqrt_pos.mp hbpos
  have hnear : ∀ᶠ x in 𝓝 t, 0 < S x :=
    hS.continuous.continuousAt.eventually (eventually_gt_nhds hSt)
  have hb (x : ℝ) (hx : 0 < S x) : ContDiffAt ℝ 3 b x :=
    (Real.contDiffAt_sqrt hx.ne').comp x hS.contDiffAt
  have hbD (x : ℝ) (hx : 0 < S x) : DifferentiableAt ℝ b x :=
    (hb x hx).differentiableAt (by decide)
  have hbD₁ (x : ℝ) (hx : 0 < S x) : DifferentiableAt ℝ (deriv b) x :=
    ((hb x hx).derivWithin (show (2 : WithTop ℕ∞) + 1 ≤ 3 by decide)).differentiableAt (by decide)
  have hbD₂ : DifferentiableAt ℝ (deriv (deriv b)) t :=
    (((hb t hSt).derivWithin (show (2 : WithTop ℕ∞) + 1 ≤ 3 by decide)).derivWithin
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)).differentiableAt (by decide)
  have hSq (x : ℝ) (hx : 0 < S x) : (fun y ↦ b y ^ 2) =ᶠ[𝓝 x] S := by
    filter_upwards [hS.continuous.continuousAt.eventually (eventually_gt_nhds hx)] with y hy
    exact Real.sq_sqrt hy.le
  have hb₁ (x : ℝ) (hx : 0 < S x) : deriv S x = 2*b x*deriv b x := by
    rw [← (hSq x hx).deriv_eq, deriv_fun_pow (hbD x hx) 2]
    simp
  have hb₂ (x : ℝ) (hx : 0 < S x) :
      deriv (deriv S) x = 2*deriv b x ^ 2 + 2*b x*deriv (deriv b) x := by
    have heq : deriv S =ᶠ[𝓝 x] fun y ↦ 2*b y*deriv b y := by
      filter_upwards [hS.continuous.continuousAt.eventually (eventually_gt_nhds hx)] with y hy
      exact hb₁ y hy
    have hd := ((hbD x hx).hasDerivAt.const_mul 2).mul (hbD₁ x hx).hasDerivAt
    change HasDerivAt (fun y ↦ 2*b y*deriv b y) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    ring
  have hb₃ : deriv (deriv (deriv S)) t =
      6*deriv b t*deriv (deriv b) t + 2*b t*deriv (deriv (deriv b)) t := by
    have heq : deriv (deriv S) =ᶠ[𝓝 t]
        fun y ↦ 2*deriv b y ^ 2 + 2*b y*deriv (deriv b) y := by
      filter_upwards [hnear] with y hy using hb₂ y hy
    have hd := (((hbD₁ t hSt).hasDerivAt.pow 2).const_mul 2).add
      (((hbD t hSt).hasDerivAt.const_mul 2).mul hbD₂.hasDerivAt)
    change HasDerivAt (fun y ↦ 2*deriv b y ^ 2 + 2*b y*deriv (deriv b) y) _ t at hd
    rw [heq.deriv_eq, hd.deriv]
    ring
  obtain ⟨hA₁pos, hA₁max, hA₂pos, hA₂max, hA₃pos, hA₃max⟩ :=
    separated_correction_derivative_bounds hh ht
  obtain ⟨hB₁pos, hB₁max, hB₂pos, hB₂max, hB₃pos, hB₃max⟩ :=
    separated_square_derivative_bounds hh hhmax ht
  have hAB : A t ≤ B t / 3400 := (separated_marginal_correction_lt hh ht).le
  have ha₀ : 0 ≤ upperTailGap h t := by
    unfold upperTailGap
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))) hh.le
  have hAt : 0 ≤ A t := by dsimp [A, separatedCorrection]; positivity
  have hBt : 0 ≤ B t := by dsimp [B, separatedSquare]; positivity
  have hα : 3+h ≤ 4 := by linarith
  have hα₀ : 0 ≤ 3+h := by linarith
  have hbound (n : ℕ) : (3+h)^n * A t ≤ 4^n * (B t / 3400) :=
    mul_le_mul (pow_le_pow_left₀ hα₀ hα n) hAB hAt (by positivity)
  have hS₁max : |deriv S t| ≤ (21/10)*B t := by
    change 0 ≤ -deriv A t at hA₁pos
    change 0 ≤ -deriv B t at hB₁pos
    rw [hS₁, abs_of_nonneg (by linarith only [hA₁pos, hB₁pos])]
    have hm := hbound 1
    simp only [pow_one] at hm
    change -deriv A t ≤ (3+h)*A t at hA₁max
    change -deriv B t ≤ 2*B t at hB₁max
    linarith only [hA₁max, hB₁max, hm, hBt]
  have hS₂max : |deriv (deriv S) t| ≤ (41/10)*B t := by
    change 0 ≤ deriv (deriv A) t at hA₂pos
    change 0 ≤ deriv (deriv B) t at hB₂pos
    rw [hS₂, abs_of_nonpos (by linarith only [hA₂pos, hB₂pos])]
    have hm := hbound 2
    change deriv (deriv A) t ≤ (3+h)^2*A t at hA₂max
    change deriv (deriv B) t ≤ 4*B t at hB₂max
    linarith only [hA₂max, hB₂max, hm, hBt]
  have hS₃max : |deriv (deriv (deriv S)) t| ≤ (81/10)*B t := by
    change 0 ≤ -deriv (deriv (deriv A)) t at hA₃pos
    change 0 ≤ -deriv (deriv (deriv B)) t at hB₃pos
    rw [hS₃, abs_of_nonneg (by linarith only [hA₃pos, hB₃pos])]
    have hm := hbound 3
    change -deriv (deriv (deriv A)) t ≤ (3+h)^3*A t at hA₃max
    change -deriv (deriv (deriv B)) t ≤ 8*B t at hB₃max
    linarith only [hA₃max, hB₃max, hm, hBt]
  have hscale (x y z M : ℝ) (heq : 2*b t*x = z-y)
      (hz : |z| + |y| ≤ (999/500)*M*B t) : |x| ≤ M*B t := by
    have hm : |2*b t*x| ≤ |z| + |y| := by rw [heq]; exact abs_sub z y
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*b t)] at hm
    have hs := mul_le_mul_of_nonneg_right hbmin (abs_nonneg x)
    linarith
  have hb₁max : |deriv b t| ≤ (13/10)*B t := by
    apply hscale _ 0 (deriv S t) _ (by rw [hb₁ t hSt, sub_zero])
    rw [abs_zero, add_zero]
    linarith only [hS₁max, hBt]
  have hb₂max : |deriv (deriv b) t| ≤ (33/10)*B t := by
    apply hscale _ (2*deriv b t^2) (deriv (deriv S) t) _ (by rw [hb₂ t hSt]; ring)
    have hm := mul_le_mul hb₁max hBmax.le hBt (by positivity : 0 ≤ (13/10)*B t)
    have hk := mul_le_mul_of_nonneg_left hb₁max (abs_nonneg (deriv b t))
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*deriv b t^2)]
    rw [← abs_mul, abs_mul_self] at hk
    nlinarith only [hS₂max, hm, hk,
      mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 13/10), hBt]
  have hb₃max : |deriv (deriv (deriv b)) t| ≤ (83/10)*B t := by
    apply hscale _ (6*deriv b t*deriv (deriv b) t) (deriv (deriv (deriv S)) t) _
      (by rw [hb₃]; ring)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    have hm := mul_le_mul hb₁max hb₂max (abs_nonneg _) (by positivity : 0 ≤ (13/10)*B t)
    have hk := mul_le_mul_of_nonneg_left hBmax.le hBt
    nlinarith only [hS₃max, hm, hk, hBt]
  exact ⟨hb₁max, hb₂max, hb₃max⟩

/-- Bounds for the root difference and its successive translation derivatives.
The factor `v - s` retains the cancellation at a repeated node. -/
theorem separated_radical_difference_bounds {h s v : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (hs : 6 ≤ s) (hsv : s ≤ v) :
    let B := ((3+h)*(3+2*h)/2) * (upperTailGap h s)^2 * Real.exp (-(2*s))
    let b : ℝ → ℝ := fun x ↦ Real.sqrt (1 - upperTailLambda h x)
    |b v - b s| ≤ (13/10)*B*(v-s) ∧
      |deriv b v - deriv b s| ≤ (33/10)*B*(v-s) ∧
      |deriv (deriv b) v - deriv (deriv b) s| ≤ (83/10)*B*(v-s) := by
  let B := separatedSquare h
  let S : ℝ → ℝ := fun x ↦ 1 - upperTailLambda h x
  let b : ℝ → ℝ := fun x ↦ Real.sqrt (S x)
  have hB : ContDiff ℝ 1 B := by unfold B separatedSquare upperTailGap; fun_prop
  have hS : ContDiff ℝ 3 S := by unfold S upperTailLambda upperTailGap; fun_prop
  have hmono : AntitoneOn B (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hB.continuous.continuousOn
      (hB.differentiable (by decide)).differentiableOn
    intro x hx
    exact neg_nonneg.mp (separated_square_derivative_bounds hh hhmax
      (interior_subset hx : x ∈ Ici (6 : ℝ))).1
  have hb (x : ℝ) (hx : 6 ≤ x) : ContDiffAt ℝ 3 b x := by
    have hpos : 0 < b x := lt_of_lt_of_le (by norm_num : 0 < (999/1000 : ℝ))
      (separated_radical_lower hh hhmax hx).2
    exact hS.contDiffAt.sqrt (Real.sqrt_pos.mp hpos).ne'
  have hb₁ (x : ℝ) (hx : 6 ≤ x) : ContDiffAt ℝ 2 (deriv b) x :=
    (hb x hx).derivWithin (by norm_num)
  have hb₂ (x : ℝ) (hx : 6 ≤ x) : ContDiffAt ℝ 1 (deriv (deriv b)) x :=
    (hb₁ x hx).derivWithin (by norm_num)
  have hMVT (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
      (hf : ∀ x, 6 ≤ x → DifferentiableAt ℝ f x)
      (hbound : ∀ x, 6 ≤ x → |deriv f x| ≤ C*B x) :
      |f v - f s| ≤ C*B s*(v-s) := by
    have hderiv (x : ℝ) (hx : x ∈ Icc s v) : ‖deriv f x‖ ≤ C*B s := by
      rw [Real.norm_eq_abs]
      have hx' := hs.trans hx.1
      exact (hbound x hx').trans (mul_le_mul_of_nonneg_left (hmono hs hx' hx.1) hC)
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (hx : x ∈ Icc s v) ↦ hf x (hs.trans hx.1)) hderiv (convex_Icc s v)
      (left_mem_Icc.mpr hsv) (right_mem_Icc.mpr hsv)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsv)] using hm
  exact ⟨hMVT b (13/10) (by norm_num) (fun x hx ↦ (hb x hx).differentiableAt (by decide))
      (fun x hx ↦ (separated_radical_derivative_bounds hh hhmax hx).1),
    hMVT (deriv b) (33/10) (by norm_num) (fun x hx ↦ (hb₁ x hx).differentiableAt (by decide))
      (fun x hx ↦ (separated_radical_derivative_bounds hh hhmax hx).2.1),
    hMVT (deriv (deriv b)) (83/10) (by norm_num) (fun x hx ↦ (hb₂ x hx).differentiableAt (by decide))
      (fun x hx ↦ (separated_radical_derivative_bounds hh hhmax hx).2.2)⟩

def leftStripWeight (h a v : ℝ) : ℝ :=
  Real.exp (logReciprocalGap h v + logReciprocalGap h (v-a)) /
    ((3+h)*(3+2*h)/2)

theorem hasDerivAt_leftStripWeight_left {h a v : ℝ} (hh : 0 < h) (hav : a < v) :
    HasDerivAt (leftStripWeight h · v) (-leftStripWeight h a v*profileSlope h (v-a)) a := by
  have hd := (hasDerivAt_logReciprocalGap hh (sub_pos.mpr hav)).comp a
    ((hasDerivAt_id' a).const_sub v)
  have hw := (hd.const_add (logReciprocalGap h v)).exp.div_const ((3+h)*(3+2*h)/2)
  change HasDerivAt (leftStripWeight h · v) _ a at hw
  exact hw.congr_deriv (by dsimp [leftStripWeight, Function.comp_def]; ring)

theorem hasDerivAt_leftStripWeight_right {h a v : ℝ} (hh : 0 < h) (hv : 0 < v) (hav : a < v) :
    HasDerivAt (leftStripWeight h a)
      (leftStripWeight h a v*(profileSlope h v+profileSlope h (v-a))) v := by
  have hd := (hasDerivAt_logReciprocalGap hh hv).add
    ((hasDerivAt_logReciprocalGap hh (sub_pos.mpr hav)).comp v ((hasDerivAt_id' v).sub_const a))
  have hw := hd.exp.div_const ((3+h)*(3+2*h)/2)
  change HasDerivAt (leftStripWeight h a) _ v at hw
  exact hw.congr_deriv (by dsimp [leftStripWeight, Function.comp_def]; ring)

/-- One factor of the leading square cancels the potentially growing weight. -/
theorem leftStrip_weight_mul_square_le {h a v : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hgap : 6 ≤ v-a) :
    let s := v-a
    let B := ((3+h)*(3+2*h)/2) * (upperTailGap h s)^2 * Real.exp (-(2*s))
    leftStripWeight h a v * B ≤ 5/3 := by
  let s := v-a
  let g := upperTailGap h
  have hsg (t : ℝ) (ht : 0 < t) : 0 < g t := by
    exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))) hh
  have hsv : s ≤ v := sub_le_self _ ha
  have hs : 0 < s := by linarith
  have hgs := hsg s hs
  have hgv := hsg v (hs.trans_le hsv)
  have hc : 0 < (3+h)*(3+2*h)/2 := by positivity
  have hg_le : g s ≤ g v := by
    unfold g upperTailGap
    exact div_le_div_of_nonneg_right (sub_le_sub_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hsv hh.le))) _) hh.le
  have heq : leftStripWeight h a v * separatedSquare h s =
      Real.exp a * (g s / g v) := by
    unfold leftStripWeight separatedSquare logReciprocalGap
    change Real.exp (v - Real.log (g v) + (s - Real.log (g s))) / _ *
      (_ * (g s)^2 * Real.exp (-(2*s))) = _
    rw [Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log hgv, Real.exp_log hgs]
    have hex : Real.exp v * Real.exp s * Real.exp (-(2*s)) = Real.exp a := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [s]
      ring
    field_simp [hgs.ne', hgv.ne', hc.ne']
    linear_combination hex
  change leftStripWeight h a v * separatedSquare h s ≤ 5/3
  rw [heq]
  exact (mul_le_of_le_one_right (Real.exp_pos a).le ((div_le_one hgv).mpr hg_le)).trans
    (((Real.exp_le_exp.mpr hamax).trans exp_half_le).trans (by norm_num))

/-- The squared difference of the marginal roots, with the same weight as
the geometric and repeat-node terms of the lower-collision profile. -/
def leftStripRadicalTerm (h a v : ℝ) : ℝ :=
  leftStripWeight h a v *
    (Real.sqrt (1 - upperTailLambda h v) - Real.sqrt (1 - upperTailLambda h (v-a)))^2 / 2

/-- The weighted third derivative of the root-difference term. The two
translated differences remain factored in the formula. -/
theorem leftStrip_radical_mixed_formula {h a v γ : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ha : 0 ≤ a) (hgap : 6 ≤ v-a) :
    let s := v-a
    let b : ℝ → ℝ := fun x ↦ Real.sqrt (1 - upperTailLambda h x)
    let Δ := b v - b s
    let Δ₁ := deriv b v - deriv b s
    let L := profileSlope h s
    let q := profileCurvature h s
    let q₁ := -q*(h+2*upperTailSlope h s)
    let b₁ := deriv b s
    let b₂ := deriv (deriv b) s
    let b₃ := deriv (deriv (deriv b)) s
    let M := b₁^2 - Δ*b₂ - 2*L*Δ*b₁ + (L^2+q)*Δ^2/2
    let M₁ := 2*b₁*b₂ - Δ₁*b₂ - Δ*b₃ - 2*q*Δ*b₁ -
      2*L*(Δ₁*b₁+Δ*b₂) + (2*L*q+q₁)*Δ^2/2 + (L^2+q)*Δ*Δ₁
    deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) x) a) v -
      γ * deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t v) x) a =
      leftStripWeight h a v * ((profileSlope h v + L - γ)*M + M₁) := by
  let S : ℝ → ℝ := fun t ↦ 1 - upperTailLambda h t
  let b : ℝ → ℝ := fun t ↦ Real.sqrt (S t)
  let W := leftStripWeight h
  let L := profileSlope h
  let q := profileCurvature h
  let δ (x y : ℝ) := b y-b (y-x)
  let M (x y : ℝ) := (deriv b (y-x))^2 - δ x y*deriv (deriv b) (y-x) -
    2*L (y-x)*δ x y*deriv b (y-x) + (L (y-x)^2+q (y-x))*(δ x y)^2/2
  have hS : ContDiff ℝ 3 S := by unfold S upperTailLambda upperTailGap; fun_prop
  have hb (x : ℝ) (hx : 0 < S x) : ContDiffAt ℝ 3 b x := hS.contDiffAt.sqrt hx.ne'
  have hb₀ (x : ℝ) (hx : 0 < S x) : HasDerivAt b (deriv b x) x :=
    ((hb x hx).differentiableAt (by decide)).hasDerivAt
  have hb₁ (x : ℝ) (hx : 0 < S x) : ContDiffAt ℝ 2 (deriv b) x :=
    (hb x hx).derivWithin (by norm_num)
  have hb₂ (x : ℝ) (hx : 0 < S x) : HasDerivAt (deriv b) (deriv (deriv b) x) x :=
    ((hb₁ x hx).differentiableAt (by decide)).hasDerivAt
  have hb₃ (x : ℝ) (hx : 0 < S x) :
      HasDerivAt (deriv (deriv b)) (deriv (deriv (deriv b)) x) x := by
    have hd : ContDiffAt ℝ 1 (deriv (deriv b)) x := (hb₁ x hx).derivWithin (by norm_num)
    exact (hd.differentiableAt (by decide)).hasDerivAt
  have hWleft (x y : ℝ) (hxy : x < y) :
      HasDerivAt (W · y) (-W x y*L (y-x)) x :=
    hasDerivAt_leftStripWeight_left hh hxy
  have hδleft (x y : ℝ) (hx : 0 < S (y-x)) :
      HasDerivAt (δ · y) (deriv b (y-x)) x := by
    have hd := (hb₀ _ hx).comp x ((hasDerivAt_id' x).const_sub y)
    have hδ := hd.const_sub (b y)
    change HasDerivAt (δ · y) _ x at hδ
    simpa only [mul_neg, mul_one, neg_neg] using hδ
  have hfirst (x y : ℝ) (hxy : x < y) (hx : 0 < S (y-x)) :
      deriv (fun t ↦ leftStripRadicalTerm h t y) x =
        W x y * (δ x y*deriv b (y-x) - L (y-x)*(δ x y)^2/2) := by
    have hd := ((hWleft x y hxy).mul ((hδleft x y hx).pow 2)).div_const 2
    change HasDerivAt (fun t ↦ leftStripRadicalTerm h t y) _ x at hd
    rw [hd.deriv]
    simp only [Pi.pow_apply]
    ring
  have hsecond (x y : ℝ) (hxy : x < y) (hx : 0 < S (y-x)) :
      deriv (fun r ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) r) x = W x y*M x y := by
    have hnear : ∀ᶠ r in 𝓝 x, 0 < S (y-r) :=
      (hS.continuous.comp (continuous_const.sub continuous_id)).continuousAt.eventually
        (eventually_gt_nhds hx)
    have heq : (fun r ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) r) =ᶠ[𝓝 x]
        fun r ↦ W r y*(δ r y*deriv b (y-r)-L (y-r)*(δ r y)^2/2) := by
      filter_upwards [eventually_lt_nhds hxy, hnear] with r h₁ h₂ using hfirst r y h₁ h₂
    have hshift := (hasDerivAt_id' x).const_sub y
    have hb' := (hb₂ _ hx).comp x hshift
    have hL := (hasDerivAt_profileSlope hh (sub_pos.mpr hxy)).comp x hshift
    have hδ := hδleft x y hx
    have hd := (hWleft x y hxy).mul
      ((hδ.mul hb').sub ((hL.mul (hδ.pow 2)).div_const 2))
    change HasDerivAt (fun r ↦ W r y*(δ r y*deriv b (y-r)-L (y-r)*(δ r y)^2/2)) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    dsimp [M, L, q]
    ring
  have hs : 0 < v-a := by linarith
  have hv : 0 < v := by linarith
  have hsv : a < v := sub_pos.mp hs
  have hpos (x : ℝ) (hx : 6 ≤ x) : 0 < S x :=
    Real.sqrt_pos.mp ((by norm_num : (0 : ℝ) < 999/1000).trans_le
      (separated_radical_lower hh hhmax hx).2)
  have hxs := hpos (v-a) hgap
  have hxv := hpos v (by linarith)
  have hnear : ∀ᶠ y in 𝓝 v, 0 < S (y-a) :=
    (hS.continuous.comp (continuous_id.sub continuous_const)).continuousAt.eventually
      (eventually_gt_nhds hxs)
  have heq : (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) x) a) =ᶠ[𝓝 v]
      fun y ↦ W a y*M a y := by
    filter_upwards [eventually_gt_nhds hsv, hnear] with y hy hys using hsecond a y hy hys
  have hshift := (hasDerivAt_id' v).sub_const a
  have hL := (hasDerivAt_profileSlope hh hs).comp v hshift
  have hq := (hasDerivAt_profileCurvature hh hs).comp v hshift
  have hδ := (hb₀ _ hxv).sub ((hb₀ _ hxs).comp v hshift)
  have hb₁s := (hb₂ _ hxs).comp v hshift
  have hb₂s := (hb₃ _ hxs).comp v hshift
  have hw := hasDerivAt_leftStripWeight_right hh hv hsv
  have hm := (((hb₁s.pow 2).sub (hδ.mul hb₂s)).sub
    (((hL.const_mul 2).mul hδ).mul hb₁s)).add
      ((((hL.pow 2).add hq).mul (hδ.pow 2)).div_const 2)
  change HasDerivAt (M a) _ v at hm
  have hd := hw.mul hm
  change HasDerivAt (fun y ↦ W a y*M a y) _ v at hd
  dsimp only
  rw [heq.deriv_eq, hd.deriv, hsecond a v hsv hxs]
  dsimp [W, M, L, q, b, S, δ, leftStripWeight]
  ring

#print axioms leftStrip_geometric_mixed_lt
#print axioms separated_radical_lower
#print axioms separated_marginal_correction_lt
#print axioms separated_square_derivative_bounds
#print axioms separated_correction_derivative_bounds
#print axioms separated_radical_derivative_bounds
#print axioms separated_radical_difference_bounds
#print axioms leftStrip_radical_mixed_formula

end RefinedBMV.PositiveCenter
