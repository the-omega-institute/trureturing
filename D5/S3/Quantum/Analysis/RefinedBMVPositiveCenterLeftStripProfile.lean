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
  have he6 : (400 : ℝ) < Real.exp 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    have ho : (2718/1000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    exact (by norm_num : (400 : ℝ) < (2718/1000)^6).trans
      (pow_lt_pow_left₀ ho (by norm_num) (by decide))
  have he6neg : Real.exp (-6) ≤ (1 : ℝ)/400 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he6.le
  have he : e ≤ 1/400 :=
    (Real.exp_le_exp.mpr (neg_le_neg ht)).trans he6neg
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
    exact hmul.trans (by linarith only [he6neg])
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

#print axioms leftStrip_geometric_mixed_lt
#print axioms separated_radical_lower

end RefinedBMV.PositiveCenter
