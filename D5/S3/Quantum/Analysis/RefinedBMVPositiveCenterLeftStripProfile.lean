/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripProfile
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative weighted third derivative of the leading profile at the lower collision. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailAverage
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The leading term for a small lower coordinate and a separated upper coordinate -/

open Filter Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

private def logReciprocalGap (h t : ℝ) : ℝ := t - Real.log (upperTailGap h t)

private def profileSlope (h t : ℝ) : ℝ := 1 - upperTailSlope h t

private def profileCurvature (h t : ℝ) : ℝ :=
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

private theorem hasDerivAt_profileSlope {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (profileSlope h) (profileCurvature h t) t := by
  change HasDerivAt (fun x ↦ 1 - upperTailSlope h x) (profileCurvature h t) t
  simpa only [profileCurvature, neg_neg] using (hasDerivAt_upperTailSlope hh ht).const_sub 1

private theorem hasDerivAt_profileCurvature {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
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

private theorem sinh_half_le : Real.sinh (1/2 : ℝ) ≤ 21/40 := by
  have he : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have hk : Real.exp (1/2 : ℝ)^2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2 : ℝ)]
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

#print axioms leftStrip_geometric_mixed_lt
#print axioms separated_radical_lower
#print axioms separated_marginal_correction_lt
#print axioms separated_square_derivative_bounds
#print axioms separated_correction_derivative_bounds

end RefinedBMV.PositiveCenter
