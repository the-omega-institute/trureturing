/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometry
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative weighted third derivative of the geometric term for left-strip gaps of at least seven halves. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripProfile

open Filter Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

private theorem geometricTerm_weighted_third {h a v γ : ℝ}
    (hh : 0 < h) (hv : 0 < v) (hav : a < v) :
    let s := v-a
    let θ := geometricAngle h a v
    let L := upperTailSlope h s
    let slope := profileSlope h s
    let q := profileCurvature h s
    let δ := profileSlope h v - slope
    deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) v -
        γ * deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) a =
      Real.cosh θ * (2*slope*q - δ*q - γ*slope^2) +
        Real.sinh θ * (δ*slope^2 + q*(h+2*L) + γ*q) := by
  let s := v-a
  let θ := geometricAngle h a v
  let L := upperTailSlope h s
  let slope := profileSlope h s
  let q := profileCurvature h s
  let δ := profileSlope h v - slope
  have hs : 0 < s := sub_pos.mpr hav
  have heq : (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) =ᶠ[𝓝 v]
      (fun y ↦ Real.cosh (geometricAngle h a y) * profileSlope h (y-a)^2 -
        Real.sinh (geometricAngle h a y) * profileCurvature h (y-a)) := by
    filter_upwards [eventually_gt_nhds hav] with y hy
    exact geometricTerm_left_second hh hy
  have hDθ := hasDerivAt_geometricAngle_right hh hv hav
  have hDslope := (hasDerivAt_profileSlope hh hs).comp v ((hasDerivAt_id' v).sub_const a)
  have hDq := (hasDerivAt_profileCurvature hh hs).comp v ((hasDerivAt_id' v).sub_const a)
  have hd := (hDθ.cosh.mul (hDslope.pow 2)).sub (hDθ.sinh.mul hDq)
  change HasDerivAt (fun y ↦ Real.cosh (geometricAngle h a y) * profileSlope h (y-a)^2 -
      Real.sinh (geometricAngle h a y) * profileCurvature h (y-a)) _ v at hd
  rw [heq.deriv_eq, geometricTerm_left_second hh hav, hd.deriv]
  dsimp [θ, δ, slope, q, L, s]
  ring

private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x*Real.cosh x := by
  let f (t : ℝ) := t*Real.cosh t-Real.sinh t
  have hd (t : ℝ) : HasDerivAt f (t*Real.sinh t) t := by
    convert (((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t)) using 1
    simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
    · rw [interior_Ici]
      exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
    rw [interior_Ici]
    intro t ht
    rw [(hd t).deriv]
    exact mul_nonneg ht.le (Real.sinh_nonneg_iff.mpr ht.le)
  have hzero : (0 : ℝ) ∈ Ici 0 := by simp
  have h := hm hzero (show x ∈ Ici 0 from hx) hx
  simpa [f, sub_nonneg] using h

/-- Uniform geometric margin for gaps of at least seven halves. -/
theorem leftStrip_geometric_seven_halves_lt {h a v γ : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ha : 0 ≤ a) (hamax : a ≤ 1/2)
    (hgap : 7/2 ≤ v-a) (hγ : 5/12 ≤ γ) :
    deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t y) x) a) v -
      γ * deriv (fun x ↦ deriv (fun t ↦ leftStripGeometricTerm h t v) x) a < -49/1000 := by
  let s := v-a
  let θ := geometricAngle h a v
  let L := profileSlope h s
  let q := profileCurvature h s
  let δ := profileSlope h v-L
  have hs : 0 < s := by linarith
  have hsv : s ≤ v := sub_le_self _ ha
  have hv : 0 < v := hs.trans_le hsv
  have haEq : v-s = a := by dsimp [s]; ring
  have hL (t : ℝ) (ht : s ≤ t) : 5/7 ≤ profileSlope h t ∧ profileSlope h t ≤ 1 := by
    obtain ⟨hH₀, hH, _⟩ := upperTailSlope_bounds hh (hs.trans_le ht)
    have h := hH.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7/2) (hgap.trans ht))
    unfold profileSlope
    constructor <;> linarith
  have hqpos (t : ℝ) (ht : s ≤ t) : 0 ≤ profileCurvature h t := by
    have hH := (upperTailSlope_bounds hh (hs.trans_le ht)).1
    unfold profileCurvature
    positivity
  have hqmax : q ≤ 4/49 := by
    obtain ⟨_, _, _, hq, _⟩ := upperTailSlope_bounds hh hs
    rw [(hasDerivAt_upperTailSlope hh hs).deriv, neg_neg] at hq
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7/2) hgap
    refine hq.trans ?_
    simpa only [one_div_pow, show (1/(7/2) : ℝ)^2 = 4/49 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1/s) hi 2
  have hq₀ : 0 ≤ q := hqpos s le_rfl
  have hLmono : MonotoneOn (profileSlope h) (Icc s v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht ↦ (hasDerivAt_profileSlope hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
    · rw [interior_Icc]
      exact fun t ht ↦ (hasDerivAt_profileSlope hh (hs.trans ht.1)).differentiableAt.differentiableWithinAt
    rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_profileSlope hh (hs.trans ht.1)).deriv]
    exact hqpos t ht.1.le
  have hqanti : AntitoneOn (profileCurvature h) (Icc s v) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t ht ↦ (hasDerivAt_profileCurvature hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
    · rw [interior_Icc]
      exact fun t ht ↦ (hasDerivAt_profileCurvature hh (hs.trans ht.1)).differentiableAt.differentiableWithinAt
    rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_profileCurvature hh (hs.trans ht.1)).deriv]
    have hH := (upperTailSlope_bounds hh (hs.trans ht.1)).1
    exact neg_nonpos.mpr (mul_nonneg (hqpos t ht.1.le) (by positivity))
  have hδ : 0 ≤ δ ∧ δ ≤ q/2 := by
    rcases hsv.eq_or_lt with he | hlt
    · have hz : δ = 0 := by
        change profileSlope h v - profileSlope h s = 0
        rw [he, sub_self]
      exact ⟨hz.ge, hz ▸ div_nonneg hq₀ (by norm_num)⟩
    obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (profileSlope h) (profileCurvature h) hlt
      (fun t ht ↦ (hasDerivAt_profileSlope hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht ↦ hasDerivAt_profileSlope hh (hs.trans ht.1))
    have hEq : profileCurvature h t*a = δ := by
      rw [← haEq]; exact (eq_div_iff (sub_pos.mpr hlt).ne').mp he
    rw [← hEq]
    exact ⟨mul_nonneg (hqpos t ht.1.le) ha,
      (mul_le_mul (hqanti ⟨le_rfl, hsv⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le) hamax ha hq₀).trans_eq (by ring)⟩
  have hθ : 0 ≤ θ ∧ θ ≤ (L/2+q/4) ∧ θ ≤ 1/2 := by
    rcases hsv.eq_or_lt with he | hlt
    · have : θ = 0 := by
        change logReciprocalGap h v - logReciprocalGap h s = 0
        rw [he, sub_self]
      rw [this]
      exact ⟨le_rfl, by linarith [(hL s le_rfl).1], by norm_num⟩
    obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (logReciprocalGap h) (profileSlope h) hlt
      (fun t ht ↦ (hasDerivAt_logReciprocalGap hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht ↦ hasDerivAt_logReciprocalGap hh (hs.trans ht.1))
    have hEq : profileSlope h t*a = θ := by
      rw [← haEq]; exact (eq_div_iff (sub_pos.mpr hlt).ne').mp he
    rw [← hEq]
    have hLt := hL t ht.1.le
    have hmono := hLmono ⟨ht.1.le, ht.2.le⟩ ⟨hsv, le_rfl⟩ ht.2.le
    have hcap := mul_le_mul hmono hamax ha (by linarith [(hL v hsv).1])
    exact ⟨mul_nonneg (by linarith) ha, by linarith only [hcap, hδ.2],
      (mul_le_of_le_one_left ha hLt.2).trans hamax⟩
  have hLmin : 5/7 ≤ L := (hL s le_rfl).1
  have hLmax : L ≤ 1 := (hL s le_rfl).2
  have hLsq : (5/7 : ℝ)^2 ≤ L^2 := pow_le_pow_left₀ (by norm_num) hLmin 2
  have hHpos := (upperTailSlope_bounds hh hs).1
  have hC₀ : 0 ≤ δ*L^2+q*(h+2*upperTailSlope h s)+γ*q := by
    have hγ₀ : 0 ≤ γ := by linarith
    exact add_nonneg (add_nonneg (mul_nonneg hδ.1 (sq_nonneg L))
      (mul_nonneg hq₀ (by positivity))) (mul_nonneg hγ₀ hq₀)
  let A (l : ℝ) := l^2/2-2*l+355/132
  let Ψ (l r : ℝ) := -(5/12)*l^2+2*l*r+(l/2+r/4)*r*A l
  have hA₀ : 0 ≤ A L := by dsimp [A]; nlinarith only [hLmax, sq_nonneg L]
  have hAmax : A L ≤ 2 := by
    have hLs := mul_le_mul_of_nonneg_left hLmax (show 0 ≤ L by linarith)
    dsimp [A]; nlinarith only [hLs, hLmin]
  have hC : δ*L^2+q*(h+2*upperTailSlope h s)+(5/12)*q ≤ q*A L := by
    have h₁ := mul_le_mul_of_nonneg_right hδ.2 (sq_nonneg L)
    have h₂ := mul_le_mul_of_nonneg_left hhmax hq₀
    dsimp [A, L, profileSlope] at *
    linarith only [h₁, h₂]
  have hscaled : 2*L*q - δ*q - γ*L^2 +
      θ*(δ*L^2+q*(h+2*upperTailSlope h s)+γ*q) ≤ Ψ L q := by
    have hγcoef : θ*q-L^2 ≤ 0 := by
      have hm := mul_le_mul hθ.2.2 hqmax hq₀ (by norm_num)
      linarith only [hm, hLsq]
    have hgamma := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hγ) hγcoef
    have hcap : θ*(δ*L^2+q*(h+2*upperTailSlope h s)+(5/12)*q) ≤ (L/2+q/4)*(q*A L) :=
      (mul_le_mul_of_nonneg_left hC hθ.1).trans
        (mul_le_mul_of_nonneg_right hθ.2.1 (mul_nonneg hq₀ hA₀))
    dsimp only [Ψ]
    linarith only [hgamma, hcap, mul_nonneg hδ.1 hq₀]
  have hΨq : Ψ L q ≤ Ψ L (4/49) := by
    have hL₀ : 0 ≤ L := by linarith
    have hprod := mul_le_mul (show L/2+q/4 ≤ L/2+(4/49)/4 by linarith)
      hqmax hq₀ (by positivity)
    have hterm := mul_le_mul_of_nonneg_right hprod hA₀
    have hlin := mul_le_mul_of_nonneg_left hqmax hL₀
    dsimp only [Ψ]; linarith only [hterm, hlin]
  have hΨL : Ψ L (4/49) ≤ Ψ (5/7) (4/49) := by
    have hdiff : 0 ≤ L-5/7 := sub_nonneg.mpr hLmin
    have hA : A L ≤ A (5/7) := by
      dsimp only [A]
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos hdiff
        (show (L+5/7)/2-2 ≤ 0 by linarith)]
    have hterm := mul_le_mul_of_nonneg_left hA
      (show 0 ≤ ((5/7)/2+(4/49)/4)*(4/49 : ℝ) by norm_num)
    have hchange := mul_le_mul_of_nonneg_left hAmax
      (show 0 ≤ (L-5/7)/2 * (4/49) by positivity)
    have hsq := mul_le_mul_of_nonneg_left (show (10/7 : ℝ) ≤ L+5/7 by linarith) hdiff
    dsimp only [Ψ]; nlinarith only [hterm, hchange, hsq, hdiff]
  have hΨ : Ψ L q < -(49/1000 : ℝ) := hΨq.trans_lt (hΨL.trans_lt (by norm_num [Ψ, A]))
  have hf := geometricTerm_weighted_third (γ := γ) hh hv (sub_pos.mp hs)
  change _ = Real.cosh θ*(2*L*q-δ*q-γ*L^2) +
    Real.sinh θ*(δ*L^2+q*(h+2*upperTailSlope h s)+γ*q) at hf
  rw [hf]
  calc
    _ ≤ Real.cosh θ * Ψ L q := by
      have he := mul_le_mul_of_nonneg_right (sinh_le_mul_cosh hθ.1) hC₀
      have hm := mul_le_mul_of_nonneg_left hscaled (Real.cosh_pos θ).le
      linarith only [he, hm]
    _ < Real.cosh θ * (-(49/1000 : ℝ)) := mul_lt_mul_of_pos_left hΨ (Real.cosh_pos θ)
    _ ≤ _ := by linarith only [Real.one_le_cosh θ]

end RefinedBMV.PositiveCenter
