/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedGapRadical
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic derivative bounds for the separated-gap radical of the refined BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripProfile
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CollisionRadicand
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailMarginal

/-! # The separated-gap radical of the refined BMV kernel -/

open Filter Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

/-- The repeated-node marginal root in the quadratic correction. -/
noncomputable def upperTailRadicalRoot (h t : ℝ) : ℝ :=
  Real.sqrt (1 - upperTailLambda h t)

private noncomputable def radicalRateFactor (h t : ℝ) : ℝ :=
  (1+h)*upperTailGap h t - 1 + Real.exp (-((1+h)*t))

private noncomputable def radicalRateFactorDeriv (h t : ℝ) : ℝ :=
  (1+h)*(Real.exp (-(h*t)) - Real.exp (-((1+h)*t)))

private theorem hasDerivAt_decay (r t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-(r*s))) (-r*Real.exp (-(r*t))) t := by
  have hd : HasDerivAt (fun s : ℝ ↦ -(r*s)) (-r) t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ r*s) r t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul r
    exact HasDerivAt.neg hlin
  simpa only [mul_comm] using hd.exp

private theorem hasDerivAt_radicalRateFactor {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (radicalRateFactor h) (radicalRateFactorDeriv h t) t := by
  apply ((((hasDerivAt_upperTailGap hh).const_mul (1+h)).sub_const 1).add
    (hasDerivAt_decay (1+h) t)).congr_deriv
  unfold radicalRateFactorDeriv
  ring

private theorem hasDerivAt_radicalRateFactorDeriv (h t : ℝ) :
    HasDerivAt (radicalRateFactorDeriv h)
      ((1+h)*(-h*Real.exp (-(h*t)) + (1+h)*Real.exp (-((1+h)*t)))) t := by
  apply (((hasDerivAt_decay h t).sub (hasDerivAt_decay (1+h) t)).const_mul (1+h)).congr_deriv
  ring

private theorem upperTailRadicalRoot_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailRadicalRoot h t := by
  unfold upperTailRadicalRoot
  apply Real.sqrt_pos.mpr
  rw [one_sub_upperTailLambda_eq_collisionRadicand hh]
  have := collisionRadicand_pos h t
  positivity

private theorem hasDerivAt_upperTailRadicalRoot {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (upperTailRadicalRoot h)
      (((3+h)*(3+2*h)/2)*Real.exp (-(2*t))*upperTailGap h t*radicalRateFactor h t /
        upperTailRadicalRoot h t) t := by
  have hs : 0 < 1 - upperTailLambda h t := Real.sqrt_pos.mp (upperTailRadicalRoot_pos hh ht)
  have hd := ((hasDerivAt_upperTailLambda (t := t) hh).const_sub 1).sqrt hs.ne'
  apply hd.congr_deriv
  have hz := (upperTailRadicalRoot_pos hh ht).ne'
  change -(-(3+h)*(3+2*h)*Real.exp (-(2*t))*upperTailGap h t*radicalRateFactor h t) /
    (2*upperTailRadicalRoot h t) = _
  ring

theorem separatedGap_gap_gt {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 6 ≤ t) : 44/15 < upperTailGap h t := by
  have hmono := expGapMean_antitone hh.le hhmax (by norm_num : (0 : ℝ) ≤ 6) le_rfl
  have hgap : upperTailGap (3 / 11) 6 ≤ upperTailGap h 6 := by
    rw [expGapMean_eq (by norm_num : (0 : ℝ) < 3 / 11), expGapMean_eq hh]
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  have htime : Monotone (upperTailGap h) :=
    monotone_of_deriv_nonneg
      (fun x ↦ (hasDerivAt_upperTailGap (t := x) hh).differentiableAt)
      (fun x ↦ by rw [(hasDerivAt_upperTailGap (t := x) hh).deriv]; positivity)
  have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 18/11) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have he : (5 : ℝ) < Real.exp (18/11) := by linarith only [hexp]
  have hn : Real.exp (-(18/11 : ℝ)) < 1/5 := by
    rw [Real.exp_neg]
    exact inv_lt_of_inv_lt₀ (by norm_num) (by simpa using he)
  have h6 : (44/15 : ℝ) < upperTailGap (3 / 11) 6 := by
    unfold upperTailGap
    rw [show -((3 / 11 : ℝ)*6) = -(18/11) by norm_num]
    apply (lt_div_iff₀ (by norm_num)).mpr
    linarith only [hn]
  exact (h6.trans_le hgap).trans_le (htime ht)

private theorem hasDerivAt_radicalRootDeriv {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hH : 0 < radicalRateFactor h t) :
    let z := upperTailRadicalRoot h
    let T := deriv z
    let rho := -2 + upperTailSlope h t +
      radicalRateFactorDeriv h t / radicalRateFactor h t - T t / z t
    HasDerivAt T (T t * rho) t := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  let H := radicalRateFactor h
  let a := upperTailGap h
  let c := (3+h)*(3+2*h)/2
  have hz := upperTailRadicalRoot_pos hh ht
  have ha := tail_gap_pos hh ht
  have hT : T =ᶠ[𝓝 t] (fun s ↦ c*Real.exp (-(2*s))*a s*H s / z s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_upperTailRadicalRoot hh hs).deriv
  have htval := hT.eq_of_nhds
  have hE := (hasDerivAt_decay 2 t).const_mul c
  have haD := hasDerivAt_upperTailGap (t := t) hh
  have hHd := hasDerivAt_radicalRateFactor (t := t) hh
  have hzD : HasDerivAt z (T t) t :=
    (hasDerivAt_upperTailRadicalRoot hh ht).differentiableAt.hasDerivAt
  have hD := ((hE.mul haD).mul hHd).div hzD hz.ne'
  change HasDerivAt (fun s ↦ c*Real.exp (-(2*s))*a s*H s / z s) _ t at hD
  apply (hD.congr_of_eventuallyEq hT).congr_deriv
  have hL : Real.exp (-(h*t)) / a t = upperTailSlope h t := by
    rw [← haD.deriv]
    exact upperTailGap_logDeriv hh ht
  change _ = T t * (-2 + upperTailSlope h t + radicalRateFactorDeriv h t / H t - T t / z t)
  have hz₀ : z t ≠ 0 := hz.ne'
  have ha₀ : a t ≠ 0 := ha.ne'
  have hH₀ : H t ≠ 0 := hH.ne'
  simp only [Pi.mul_apply]
  change (((c*(-2*Real.exp (-(2*t)))*a t + c*Real.exp (-(2*t))*Real.exp (-(h*t)))*H t +
      c*Real.exp (-(2*t))*a t*radicalRateFactorDeriv h t)*z t -
      c*Real.exp (-(2*t))*a t*H t*T t) / (z t)^2 = _
  rw [← hL, htval]
  field_simp [hz₀, ha₀, hH₀]

/-- On every gap at least six the root derivative is positive, its logarithmic
slope lies in the stated uniform interval, and the slope has a uniform lower
derivative bound. -/
theorem separatedGap_radical_logDeriv_bounds {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 6 ≤ t) :
    let T := deriv (upperTailRadicalRoot h)
    let rho := fun s ↦ deriv T s / T s
    0 < T t ∧ DifferentiableAt ℝ T t ∧ DifferentiableAt ℝ rho t ∧
      -(21/10 : ℝ) ≤ rho t ∧ rho t ≤ -(47/30 : ℝ) ∧
      -(89/900 : ℝ) ≤ deriv rho t ∧ -(89/25 : ℝ)/t^2 ≤ deriv rho t := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  let rho := fun s ↦ deriv T s / T s
  let a := upperTailGap h
  let H := radicalRateFactor h
  let K := radicalRateFactorDeriv h
  let L := upperTailSlope h
  let j := 1+h
  let c := (3+h)*(3+2*h)/2
  let x := c*(a t)^2*Real.exp (-(2*t))
  have ht₀ : 0 < t := by linarith
  have hj : 0 < j := by dsimp [j]; positivity
  have ha := separatedGap_gap_gt hh hhmax ht
  have ha₀ : 0 < a t := by linarith
  have hja : 44/15 < j*a t := by
    have hp := mul_pos hh ha₀
    dsimp [j]
    linarith only [hp, ha]
  have hH₁ : j*a t - 1 ≤ H t := by
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hH : 0 < H t := by linarith
  have hHupper : H t ≤ j*a t := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hj.le ht₀.le))
    change j*a t - 1 + Real.exp (-(j*t)) ≤ j*a t
    linarith only [he]
  have hratio : j*a t ≤ (8/5)*H t := by linarith only [hH₁, hja]
  have hKpos : 0 < K t := by
    apply mul_pos hj
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    change -(j*t) < -(h*t)
    dsimp [j]
    linarith only [ht₀]
  have hLmul : Real.exp (-(h*t)) = L t*a t := by
    have hf := upperTailGap_logDeriv hh ht₀
    rw [(hasDerivAt_upperTailGap hh).deriv] at hf
    exact (div_eq_iff ha₀.ne').mp hf
  obtain ⟨hLpos, hLbound, _, hq, _, _⟩ := upperTailSlope_bounds hh ht₀
  have hLmax : L t ≤ 1/6 := hLbound.trans (one_div_le_one_div_of_le (by norm_num) ht)
  have hqmax : L t*(h+L t) ≤ 1/t^2 := by
    simpa only [(hasDerivAt_upperTailSlope hh ht₀).deriv, neg_neg] using hq
  have hKmax : K t / H t ≤ (8/5)*L t := by
    apply (div_le_iff₀ hH).mpr
    have h₁ : K t ≤ j*Real.exp (-(h*t)) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) hj.le
    rw [hLmul] at h₁
    have h₂ := mul_le_mul_of_nonneg_left hratio hLpos.le
    linarith only [h₁, h₂, show j*(L t*a t) = L t*(j*a t) by ring,
      show L t*(8/5*H t) = 8/5*L t*H t by ring]
  let K₁ := j*(-h*Real.exp (-(h*t)) + j*Real.exp (-(j*t)))
  have hK₁ := hasDerivAt_radicalRateFactorDeriv h t
  change HasDerivAt K K₁ t at hK₁
  have hKmin : -(8/5)*h*L t ≤ K₁ / H t := by
    apply (le_div_iff₀ hH).mpr
    have h₁ := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr (mul_nonneg hh.le hLpos.le))
    have h₂ : j*(-h*Real.exp (-(h*t))) ≤ K₁ := by
      dsimp [K₁]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hj.le
    rw [hLmul] at h₂
    nlinarith only [h₁, h₂]
  have hz := upperTailRadicalRoot_pos hh ht₀
  obtain ⟨hx, hzlower⟩ := separated_radical_lower hh hhmax ht
  change x < 1/750 at hx
  change (999/1000 : ℝ) ≤ z t at hzlower
  have hzD := hasDerivAt_upperTailRadicalRoot hh ht₀
  have hTval : T t = c*Real.exp (-(2*t))*a t*H t / z t := hzD.deriv
  have hT : 0 < T t := by rw [hTval]; dsimp [c]; positivity
  have hTz : T t / z t ≤ 1/10 := by
    have hNum := mul_le_mul_of_nonneg_left hHupper
      (show 0 ≤ c*Real.exp (-(2*t))*a t by dsimp [c]; positivity)
    have hzsq : (999/1000 : ℝ)^2 ≤ (z t)^2 :=
      pow_le_pow_left₀ (by norm_num) hzlower 2
    have hjx : j*x ≤ (14/11)*(1/750) := by
      apply mul_le_mul (show j ≤ 14/11 by dsimp [j]; linarith) hx.le
      · dsimp [x, c]; positivity
      · norm_num
    rw [hTval, div_div]
    apply (div_le_iff₀ (mul_pos hz hz)).mpr
    dsimp only [x] at hjx
    nlinarith only [hNum, hzsq, hjx]
  let R : ℝ → ℝ := fun s ↦ -2 + L s + K s / H s - T s / z s
  have hTd : HasDerivAt T (T t * R t) t := hasDerivAt_radicalRootDeriv hh ht₀ hH
  have hnear : rho =ᶠ[𝓝 t] R := by
    have hHcont : Continuous (radicalRateFactor h) :=
      continuous_iff_continuousAt.mpr fun s ↦
        (hasDerivAt_radicalRateFactor (t := s) hh).continuousAt
    have hTnear : ∀ᶠ s in 𝓝 t, 0 < T s := hTd.continuousAt.eventually (eventually_gt_nhds hT)
    filter_upwards [eventually_gt_nhds ht₀, hTnear,
      hHcont.continuousAt.eventually (eventually_gt_nhds hH)] with s hs hsT hsH
    change deriv T s / T s = R s
    rw [(hasDerivAt_radicalRootDeriv hh hs hsH).deriv]
    exact mul_div_cancel_left₀ _ hsT.ne'
  have hmin : -(21/10 : ℝ) ≤ R t := by
    dsimp only [R]
    linarith only [hLpos, div_pos hKpos hH, hTz]
  have hmax : R t ≤ -(47/30 : ℝ) := by
    dsimp only [R]
    linarith only [hLmax, hKmax, div_pos hT hz]
  have hZratio := hTd.div (hzD.congr_deriv hTval.symm) hz.ne'
  have hZnonpos : (T t * R t * z t - T t * T t) / z t ^ 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hT.le (by linarith only [hmax])) hz.le).trans
      (mul_nonneg hT.le hT.le))
  have hHK := hK₁.div (hasDerivAt_radicalRateFactor hh) hH.ne'
  have hD := (((hasDerivAt_upperTailSlope hh ht₀).const_add (-2)).add hHK).sub hZratio
  change HasDerivAt R _ t at hD
  have hrD := hD.congr_of_eventuallyEq hnear
  have hHKvalue : (K₁ * H t - K t * K t) / H t ^ 2 = K₁ / H t - (K t / H t)^2 := by
    field_simp [hH.ne']
  have hKsq := pow_le_pow_left₀ (div_pos hKpos hH).le hKmax 2
  have hqbase : 0 ≤ h*L t := mul_nonneg hh.le hLpos.le
  change 0 < T t ∧ DifferentiableAt ℝ T t ∧ DifferentiableAt ℝ rho t ∧
    -(21/10 : ℝ) ≤ rho t ∧ rho t ≤ -(47/30 : ℝ) ∧
      -(89/900 : ℝ) ≤ deriv rho t ∧ -(89/25 : ℝ)/t^2 ≤ deriv rho t
  rw [hnear.eq_of_nhds, hrD.deriv, hHKvalue]
  have hcurv : -(89/25 : ℝ)/t^2 ≤ -(L t*(h+L t)) +
      (K₁/H t - (K t/H t)^2) - (T t*R t*z t - T t*T t)/(z t)^2 := by
    have hscaled := mul_le_mul_of_nonneg_left hqmax (by norm_num : (0 : ℝ) ≤ 89/25)
    rw [← mul_div_assoc] at hscaled
    rw [show -(89/25 : ℝ)/t^2 = -((89/25 : ℝ)/t^2) by ring]
    nlinarith only [hscaled, hKmin, hKsq, hqbase, hZnonpos]
  refine ⟨hT, hTd.differentiableAt, hrD.differentiableAt, hmin, hmax, ?_, hcurv⟩
  apply le_trans _ hcurv
  have hsq : (36 : ℝ) ≤ t^2 := by
    nlinarith only [mul_nonneg (show 0 ≤ t-6 by linarith) (show 0 ≤ t+6 by linarith)]
  have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 36) hsq
  linarith only [mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 89/25),
    show -(89/25 : ℝ)/t^2 = -(89/25)*(1/t^2) by ring]

private theorem sub_le_sub_of_derivatives {f g f' g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Icc a b, f' t ≤ g' t) : f b - f a ≤ g b - g a := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) := (hg t ht).sub (hf t ht)
  have hm : MonotoneOn (g - f) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact sub_nonneg.mpr (hle t (interior_subset ht))
  have hv := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  change g a - f a ≤ g b - f b at hv
  linarith only [hv]

/-- Compare the divided difference of the root's derivative to its logarithmic
slope at the left endpoint, with curvature integrated at the actual gaps. -/
theorem separatedGap_radical_dividedDifference_bounds {h d v : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hd : 6 ≤ d) (hdv : d < v) :
    let z := upperTailRadicalRoot h
    let T := deriv z
    let rho := fun s ↦ deriv T s / T s
    let D := z v - z d
    0 < D ∧
      (T v-T d)/D ≤ -(47/30 : ℝ) ∧
      rho d - (T v-T d)/D ≤ (89/25)*(v-d)/(d*v) ∧
      (47/30)/(1-Real.exp (-((47/30)*(v-d)))) ≤ T d/D ∧
      T d/D ≤ 1/(v-d) + 21/10 := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  let rho := fun s ↦ deriv T s / T s
  let D := z v-z d
  let rate : ℝ := 47/30
  let ν : ℝ := 21/10
  let k : ℝ := (89/25)*(v-d)/(d*v)
  have hd₀ : 0 < d := by linarith
  have hv : 0 < v := hd₀.trans hdv
  have hz (t : ℝ) (ht : 6 ≤ t) : HasDerivAt z (T t) t :=
    (hasDerivAt_upperTailRadicalRoot hh (by linarith)).differentiableAt.hasDerivAt
  have hs (t : ℝ) (ht : 6 ≤ t) :
      0 < T t ∧ DifferentiableAt ℝ T t ∧ DifferentiableAt ℝ rho t ∧
      -ν ≤ rho t ∧ rho t ≤ -rate ∧ -(89/25 : ℝ)/t^2 ≤ deriv rho t := by
    obtain ⟨hp, hT, hr, hmin, hmax, _, hc⟩ := separatedGap_radical_logDeriv_bounds hh hhmax ht
    exact ⟨hp, hT, hr, hmin, hmax, hc⟩
  have hT (t : ℝ) (ht : 6 ≤ t) : HasDerivAt T (rho t*T t) t :=
    ((hs t ht).2.1.hasDerivAt).congr_deriv
      (by dsimp [rho]; rw [div_mul_cancel₀ _ (hs t ht).1.ne'])
  have hpositive : 0 < D := by
    have hm : StrictMonoOn z (Ici 6) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici _)
      · exact fun t ht ↦ (hz t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [(hz t (interior_subset ht)).deriv]
        exact (hs t (interior_subset ht)).1
    exact sub_pos.mpr (hm hd (hd.trans hdv.le) hdv)
  have hcurv (s : ℝ) (hs' : s ∈ Icc d v) : rho d - k ≤ rho s := by
    let r : ℝ → ℝ := fun t ↦ (89/25)/t
    have hr (t : ℝ) (ht : t ∈ Icc d s) : HasDerivAt r (-(89/25 : ℝ)/t^2) t := by
      have hdif := ((hasDerivAt_const t (89/25 : ℝ)).div (hasDerivAt_id' t)
        (hd₀.trans_le ht.1).ne')
      apply hdif.congr_deriv
      simp
    have hc := sub_le_sub_of_derivatives hs'.1 hr
      (fun t ht ↦ (hs t (hd.trans ht.1)).2.2.1.hasDerivAt)
      (fun t ht ↦ (hs t (hd.trans ht.1)).2.2.2.2.2)
    have hrv : r d-r v = k := by dsimp [r, k]; field_simp [hd₀.ne', hv.ne']
    have hrs : r v ≤ r s :=
      div_le_div_of_nonneg_left (by norm_num) (hd₀.trans_le hs'.1) hs'.2
    linarith only [hc, hrv, hrs]
  have hmeanUpper : (T v-T d)/D ≤ -rate := by
    apply (div_le_iff₀ hpositive).mpr
    have hi := sub_le_sub_of_derivatives hdv.le (fun t ht ↦ hT t (hd.trans ht.1))
      (fun t ht ↦ (hz t (hd.trans ht.1)).const_mul (-rate))
      (fun t ht ↦ mul_le_mul_of_nonneg_right (hs t (hd.trans ht.1)).2.2.2.2.1
        (hs t (hd.trans ht.1)).1.le)
    linarith only [hi, show -rate*D = -rate*z v - -rate*z d by unfold D; ring]
  have hmeanLower : rho d - (T v-T d)/D ≤ k := by
    have hi := sub_le_sub_of_derivatives hdv.le
      (fun t ht ↦ (hz t (hd.trans ht.1)).const_mul (rho d-k))
      (fun t ht ↦ hT t (hd.trans ht.1))
      (fun t ht ↦ mul_le_mul_of_nonneg_right (hcurv t ht) (hs t (hd.trans ht.1)).1.le)
    have hr : rho d-k ≤ (T v-T d)/D := (le_div_iff₀ hpositive).mpr (by
      calc
        _ = (rho d-k)*z v - (rho d-k)*z d := by unfold D; ring
        _ ≤ _ := hi)
    linarith only [hr]
  have he (r t : ℝ) : HasDerivAt (fun s ↦ Real.exp (r*(s-d)))
      (r*Real.exp (r*(t-d))) t := by
    have hl : HasDerivAt (fun s : ℝ ↦ r*(s-d)) r t := by
      simpa only [mul_one] using ((hasDerivAt_id' t).sub_const d).const_mul r
    simpa only [mul_comm] using hl.exp
  have hp (r t : ℝ) (ht : 6 ≤ t) :
      HasDerivAt (fun s ↦ Real.exp (r*(s-d))*T s)
        (Real.exp (r*(t-d))*(r+rho t)*T t) t := by
    apply ((he r t).mul (hT t ht)).congr_deriv
    ring
  have hlo (t : ℝ) (ht : t ∈ Icc d v) :
      T d*Real.exp (-(ν*(t-d))) ≤ T t := by
    have hi := sub_le_sub_of_derivatives ht.1
      (fun s _ ↦ hasDerivAt_const s (0 : ℝ)) (fun s hs' ↦ hp ν s (hd.trans hs'.1))
      (fun s hs' ↦ by
        have hh' := (hs s (hd.trans hs'.1)).2.2.2.1
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
          (hs s (hd.trans hs'.1)).1.le)
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hi
    have hi' := mul_le_mul_of_nonneg_left (sub_nonneg.mp hi) (Real.exp_pos (-(ν*(t-d)))).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hi'
    simpa only [mul_comm] using hi'
  have hhi (t : ℝ) (ht : t ∈ Icc d v) :
      T t ≤ T d*Real.exp (-(rate*(t-d))) := by
    have hi := sub_le_sub_of_derivatives ht.1
      (fun s hs' ↦ hp rate s (hd.trans hs'.1)) (fun s _ ↦ hasDerivAt_const s (0 : ℝ))
      (fun s hs' ↦ by
        have hh' := (hs s (hd.trans hs'.1)).2.2.2.2.1
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith))
          (hs s (hd.trans hs'.1)).1.le)
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hi
    have hi' := mul_le_mul_of_nonneg_left (sub_nonpos.mp hi) (Real.exp_pos (-(rate*(t-d)))).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hi'
    simpa only [mul_comm] using hi'
  have hprim (r : ℝ) (hr : 0 < r) (t : ℝ) :
      HasDerivAt (fun s ↦ T d*(1-Real.exp (-(r*(s-d))))/r)
        (T d*Real.exp (-(r*(t-d)))) t := by
    have hh' : HasDerivAt (fun s ↦ Real.exp (-(r*(s-d))))
        (-r*Real.exp (-(r*(t-d)))) t := by
      simpa only [neg_mul] using he (-r) t
    apply (((hh'.const_sub 1).const_mul (T d)).div_const r).congr_deriv
    field_simp [hr.ne']
  have hDupper := sub_le_sub_of_derivatives hdv.le
    (fun t ht ↦ hz t (hd.trans ht.1)) (fun t _ ↦ hprim rate (by norm_num [rate]) t) hhi
  have hDlower := sub_le_sub_of_derivatives hdv.le
    (fun t _ ↦ hprim ν (by norm_num [ν]) t) (fun t ht ↦ hz t (hd.trans ht.1)) hlo
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, zero_div, sub_zero] at hDupper hDlower
  have hden : 0 < 1-Real.exp (-(rate*(v-d))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos
      (mul_pos (by norm_num [rate]) (sub_pos.mpr hdv))))
  refine ⟨hpositive, hmeanUpper, hmeanLower, ?_, ?_⟩
  · apply (div_le_div_iff₀ hden hpositive).mpr
    have hm := (le_div_iff₀ (by norm_num [rate] : 0 < rate)).mp hDupper
    simpa only [mul_comm] using hm
  · apply (div_le_iff₀ hpositive).mpr
    have hu : 0 < v-d := sub_pos.mpr hdv
    have he₁ : 1+ν*(v-d) ≤ Real.exp (ν*(v-d)) := by
      linarith only [Real.add_one_le_exp (ν*(v-d))]
    have hm := mul_le_mul_of_nonneg_right he₁ (Real.exp_pos (-(ν*(v-d)))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
    let e := Real.exp (-(ν*(v-d)))
    change (1+ν*(v-d))*e ≤ 1 at hm
    have hscalar : 1 ≤ (1/(v-d)+ν) * ((1-e)/ν) := by
      have hn : 0 < ν := by norm_num [ν]
      field_simp [hu.ne', hn.ne']
      nlinarith only [hm]
    calc
      T d = T d*1 := by ring
      _ ≤ T d*((1/(v-d)+ν) * ((1-Real.exp (-(ν*(v-d))))/ν)) :=
        mul_le_mul_of_nonneg_left hscalar (hs d hd).1.le
      _ = (1/(v-d)+ν) * (T d*(1-Real.exp (-(ν*(v-d))))/ν) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hDlower
        (add_nonneg (one_div_nonneg.mpr hu.le) (by norm_num [ν]))

private theorem scaled_exponential_ratio_lower {u r : ℝ} (hu : 0 < u) (hr : 1 ≤ r) :
    1/(1-Real.exp (-u)) + (r-1)/2 ≤ r/(1-Real.exp (-(r*u))) := by
  let e : ℝ → ℝ := fun t ↦ 1-Real.exp (-t)
  let f : ℝ → ℝ := fun t ↦ t/e t - t/2
  have he (t : ℝ) (ht : 0 < t) : 0 < e t :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt f (((e t - t*Real.exp (-t)) / (e t)^2) - 1/2) t := by
    have he' : HasDerivAt e (Real.exp (-t)) t := by
      simpa only [e, neg_one_mul, one_mul, neg_neg, zero_sub] using
        (hasDerivAt_decay 1 t).const_sub 1
    have hf := ((hasDerivAt_id' t).div he' (he t ht).ne').sub
      ((hasDerivAt_id' t).div_const 2)
    convert hf using 1
    ring
  have hmono : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : 0 < t := interior_subset ht
      rw [(hd t ht₀).deriv]
      apply sub_nonneg.mpr
      apply (le_div_iff₀ (sq_pos_of_pos (he t ht₀))).mpr
      have hs := Real.self_le_sinh_iff.mpr ht₀.le
      rw [Real.sinh_eq] at hs
      have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-t)).le
      have hexp : Real.exp t*Real.exp (-t) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rw [sub_div, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, hexp] at hm
      dsimp only [e]
      nlinarith only [hm]
  have hru : 0 < r*u := mul_pos (by linarith) hu
  have huv : u ≤ r*u := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr) hu.le]
  have hm := mul_le_mul_of_nonneg_right (hmono hu hru huv) (inv_nonneg.mpr hu.le)
  change (u/e u - u/2)*u⁻¹ ≤ (r*u/e (r*u) - r*u/2)*u⁻¹ at hm
  have hleft : (u/e u - u/2)*u⁻¹ = 1/e u - 1/2 := by
    field_simp [hu.ne', (he u hu).ne']
  have hright : (r*u/e (r*u) - r*u/2)*u⁻¹ = r/e (r*u) - r/2 := by
    field_simp [hu.ne', (he (r*u) hru).ne']
  rw [hleft, hright] at hm
  linarith only [hm]

private theorem radical_left_slope_lower {u R α J b : ℝ} (hu : 0 < u)
    (hR : (47 / 30) / (1 - Real.exp (-((47 / 30) * u))) ≤ R)
    (hJ : J ≤ 3 / 2) (hb : 1 / 4 ≤ b) (hbdef : b = α + 1 / 2 + 2 / (Real.exp u - 1)) :
    49/60 ≤ α-J+2*R := by
  have hratio := (scaled_exponential_ratio_lower hu (by norm_num : (1 : ℝ) ≤ 47/30)).trans hR
  have he₀ := (Real.exp_pos u).ne'
  have he₁ : (1-Real.exp (-u)) ≠ 0 :=
    sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)).ne'
  have he₂ : Real.exp u-1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hu).ne'
  have he : 1/(1-Real.exp (-u)) = 1+1/(Real.exp u-1) := by
    rw [Real.exp_neg] at he₁ ⊢
    field_simp [he₀, he₁, he₂]
    ring
  rw [he] at hratio
  simp only [div_eq_mul_inv] at hratio hbdef
  linarith only [hratio, hJ, hb, hbdef]

private theorem radical_curvature_error {u d v R e : ℝ}
    (hu : 0 < u) (hu₄ : u ≤ 4) (hd : 6 ≤ d) (hv : v = d + u)
    (hR₀ : 0 ≤ R) (hR : R ≤ 1 / u + 21 / 10) (he : e ≤ (89 / 25) * u / (d * v)) :
    2 * R * e ≤ 4183 / 3750 := by
  have hD : 0 < d*v := mul_pos (by linarith) (by linarith)
  have hU : R*u ≤ 1+(21/10)*u := by
    have hm := mul_le_mul_of_nonneg_right hR hu.le
    rw [add_mul, one_div_mul_cancel hu.ne'] at hm
    exact hm
  have hdv : 6*(6+u) ≤ d*v := by
    rw [hv]
    have ha : (6 : ℝ) + u ≤ d+u := by linarith only [hd]
    have hb : 0 ≤ (6 : ℝ)+u := by linarith only [hu]
    exact mul_le_mul hd ha hb (show 0 ≤ d by linarith only [hd])
  have hcap : 2*(89/25)*(1+(21/10)*u) ≤ (4183/3750)*(d*v) := calc
    _ ≤ (4183/3750)*(6*(6+u)) := by linarith only [hu₄]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdv (by norm_num)
  calc
    _ ≤ (2*R)*((89/25)*u/(d*v)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = (2*(89/25)*(R*u))/(d*v) := by ring
    _ ≤ _ := (div_le_iff₀ hD).mpr
      ((mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 2*(89/25))).trans hcap)

private noncomputable def radicalLeftFactor (p : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u/2) / Real.sqrt (compositionMoment p 0 (-u))

private noncomputable def radicalUpperFactor (p : ℕ) (h v : ℝ) : ℝ :=
  (1/Real.sqrt (upperTailNormalizer (p+1) h (((p+2).choose 2 : ℝ)/(p+1)) v)) *
    (1/Real.sqrt (1-Real.exp (-(h*v))))

private noncomputable def radicalGapFactor (h d : ℝ) : ℝ :=
  Real.exp (3*d/2) / upperTailGap h d

private theorem radicalLeftFactor_jet {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    let C : ℝ → ℝ := fun s ↦ compositionMoment p 0 (-s)
    let α := 1/2 - (deriv C u/C u)/2
    0 < radicalLeftFactor p u ∧
      HasDerivAt (radicalLeftFactor p) (radicalLeftFactor p u * α) u := by
  let C : ℝ → ℝ := fun s ↦ compositionMoment p 0 (-s)
  have hC : 0 < C u := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hc : HasDerivAt C (deriv C u) u := by
    have heq : C =ᶠ[𝓝 u] (fun x ↦ x^2 * SmallCorner.G p 1 (-x)) := by
      filter_upwards [eventually_ne_nhds hu.ne'] with x hx
      unfold C SmallCorner.G
      field_simp [hx]
    have hg := SmallCorner.hasDerivAt_G p one_ne_zero (neg_ne_zero.mpr hu.ne')
    have hg' := hg.comp u (HasDerivAt.neg (hasDerivAt_id' u))
    have hprod := (hasDerivAt_pow 2 u).mul hg'
    exact (hprod.congr_of_eventuallyEq heq).differentiableAt.hasDerivAt
  have hExp : HasDerivAt (fun s : ℝ ↦ Real.exp (s/2)) (Real.exp (u/2)/2) u := by
    simpa only [mul_comm, div_eq_mul_inv, one_mul, mul_one] using
      ((hasDerivAt_id' u).div_const 2).exp
  have hS := Real.sqrt_pos.mpr hC
  refine ⟨div_pos (Real.exp_pos _) hS, ?_⟩
  apply (hExp.div (hc.sqrt hC.ne') hS.ne').congr_deriv
  change (Real.exp (u/2)/2*Real.sqrt (C u) - Real.exp (u/2)*
    (deriv C u/(2*Real.sqrt (C u)))) / Real.sqrt (C u)^2 =
      Real.exp (u/2)/Real.sqrt (C u)*(1/2-(deriv C u/C u)/2)
  rw [show deriv C u/C u = deriv C u/Real.sqrt (C u)^2 by rw [Real.sq_sqrt hC.le]]
  field_simp [hS.ne']

private theorem radicalUpperFactor_jet {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 1 ≤ v) :
    let h : ℝ := 3/(p : ℝ)
    0 < radicalUpperFactor p h v ∧ ∃ β ≤ 0,
      HasDerivAt (radicalUpperFactor p h) (radicalUpperFactor p h v * β) v := by
  let h : ℝ := 3/(p : ℝ)
  let A := upperTailNormalizer (p+1) h (((p+2).choose 2 : ℝ)/(p+1))
  let S : ℝ → ℝ := fun t ↦ 1/Real.sqrt (A t)
  let e : ℝ → ℝ := fun t ↦ 1-Real.exp (-(h*t))
  let V : ℝ → ℝ := fun t ↦ 1/Real.sqrt (e t)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hv₀ : 0 < v := by linarith
  have he : 0 < e v :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv₀)))
  have hA : 0 < A v := by
    have hl := upperTail_lower_weight hp v 0
    have hu := upperTail_upper_weight hp hv₀
    have hC := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv₀.ne')
    dsimp only at hl
    simp only [zero_add, neg_zero, zero_div, Real.exp_zero, mul_zero] at hl
    change (1-(Real.exp (-v/(p : ℝ)))^3)*DimThree.defect p (Real.exp (-v/(p : ℝ))) 1 1 =
      (p+1 : ℝ)*A v at hu
    rw [hl, (tail_cube_pow hp v).1] at hu
    have hn : 0 < ((p+2).choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ p+2 by omega)
    have hprod : 0 < (p+1 : ℝ)*A v :=
      hu ▸ mul_pos he (mul_pos (mul_pos hn (Real.exp_pos _)) hC)
    exact pos_of_mul_pos_right hprod (by positivity)
  obtain ⟨s', hs', hsD⟩ := upperTail_normalizer_invSqrt hh (by positivity) hv hA
  have heD : HasDerivAt e (h*Real.exp (-(h*v))) v := by
    simpa only [e, neg_mul, neg_neg] using (hasDerivAt_decay h v).const_sub 1
  have hS : 0 < S v := one_div_pos.mpr (Real.sqrt_pos.mpr hA)
  have hV : 0 < V v := one_div_pos.mpr (Real.sqrt_pos.mpr he)
  have hVe := (hasDerivAt_const v (1 : ℝ)).div (heD.sqrt he.ne') (Real.sqrt_pos.mpr he).ne'
  let v' := (0*Real.sqrt (e v) - 1*(h*Real.exp (-(h*v))/(2*Real.sqrt (e v)))) /
    Real.sqrt (e v)^2
  have hv' : v' ≤ 0 := by
    dsimp only [v']
    rw [zero_mul, one_mul, zero_sub]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
  let F := radicalUpperFactor p h
  have hF : 0 < F v := mul_pos hS hV
  have hF' : HasDerivAt F (s'*V v + S v*v') v := hsD.mul hVe
  refine ⟨hF, (s'*V v+S v*v')/F v, ?_, hF'.congr_deriv ?_⟩
  · exact div_nonpos_of_nonpos_of_nonneg (add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hs' hV.le) (mul_nonpos_of_nonneg_of_nonpos hS.le hv')) hF.le
  · change s'*V v+S v*v' = F v*((s'*V v+S v*v')/F v)
    exact (mul_div_cancel_left₀ (s'*V v+S v*v') hF.ne').symm.trans (mul_div_assoc _ _ _)

private theorem radicalGapFactor_jet {h d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    let J := radicalGapFactor h
    let j := 3/2 - upperTailSlope h d
    0 < J d ∧ HasDerivAt J (J d*j) d := by
  have ha := tail_gap_pos hh hd
  have haD := hasDerivAt_upperTailGap (t := d) hh
  have hL := upperTailGap_logDeriv hh hd
  have hExp : HasDerivAt (fun s : ℝ ↦ Real.exp (3*s/2))
      (3/2*Real.exp (3*d/2)) d := by
    have hl : HasDerivAt (fun s : ℝ ↦ 3*s/2) (3/2) d := by
      simpa only [mul_one] using (((hasDerivAt_id' d).const_mul 3).div_const 2)
    simpa only [mul_comm] using hl.exp
  refine ⟨div_pos (Real.exp_pos _) ha, (hExp.div haD ha.ne').congr_deriv ?_⟩
  change _ = Real.exp (3*d/2)/upperTailGap h d*(3/2-upperTailSlope h d)
  rw [← hL, haD.deriv]
  field_simp [ha.ne']

private noncomputable def radicalFactorization (p : ℕ) (h u v : ℝ) : ℝ :=
  radicalLeftFactor p u * radicalUpperFactor p h v *
    radicalGapFactor h (v-u) * (upperTailRadicalRoot h v-upperTailRadicalRoot h (v-u))^2

/-- The radical summand of the exact normalized tail decomposition in the
independent coordinates u and v. -/
noncomputable def separatedGapRadicalContribution (p : ℕ) (u v : ℝ) : ℝ :=
  let h : ℝ := 3/(p : ℝ)
  let d := v-u
  (1/Real.sqrt (upperTailNormalizer (p+1) h (((p+2).choose 2 : ℝ)/(p+1)) v)) *
    upperTailBaseFactor p u d * upperTailQuadratic h u d

private theorem separatedGapRadicalContribution_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hd : 0 < v - u) :
    let h : ℝ := 3/(p : ℝ)
    let c := (3+h)*(3+2*h)/2
    separatedGapRadicalContribution p u v =
      (h*Real.sqrt (((p+2).choose 2 : ℝ)/(p+1))/(2*c))*radicalFactorization p h u v := by
  let h : ℝ := 3/(p : ℝ)
  let d := v-u
  let c := (3+h)*(3+2*h)/2
  let N : ℝ := (p+2).choose 2
  let a := upperTailGap h
  let ell := 1-Real.exp (-u)
  let C := compositionMoment p 0 (-u)
  let A := upperTailNormalizer (p+1) h (N/(p+1)) v
  let Z := upperTailRadicalRoot h v-upperTailRadicalRoot h d
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ha := tail_gap_pos hh hd
  have he := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hv : d+u = v := by dsimp [d]; ring
  have hExp : Real.exp (3*d/2)*Real.exp (-(2*d)) = Real.exp (-d/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : upperTailRootDifference h u d = Z/ell := by
    unfold upperTailRootDifference
    rw [hv]
    rfl
  change (1/Real.sqrt A) * upperTailBaseFactor p u d * upperTailQuadratic h u d = _
  rw [upperTailQuadratic, hroot, upperTailBaseFactor]
  change (1/Real.sqrt A) * (Real.sqrt (N/(p+1))/2 * Real.exp (-d/2) *
    ((1-Real.exp (-(h*d)))/Real.sqrt (1-Real.exp (-(h*(d+u))))) *
    (Real.exp (u/2)*ell^2/Real.sqrt C)) *
      ((Z/ell)^2*(c*(a d)^2*Real.exp (-(2*d)))⁻¹) =
    (h*Real.sqrt (N/(p+1))/(2*c)) *
      ((Real.exp (u/2)/Real.sqrt C) *
        ((1/Real.sqrt A)*(1/Real.sqrt (1-Real.exp (-(h*v))))) *
        (Real.exp (3*d/2)/a d) * Z^2)
  rw [hv, tail_gap_factor hh, ← hExp]
  have ha₀ : a d ≠ 0 := ha.ne'
  have he₀ : ell ≠ 0 := he.ne'
  simp only [mul_inv_rev, div_eq_mul_inv, mul_assoc]
  field_simp [ha₀, he₀, hc.ne', (Real.exp_pos (-(2*d))).ne']
  ring

/-- The mixed derivative of the exact radical contribution is strictly negative
on the separated strip. The derivatives use independent coordinates. -/
theorem separatedGap_radical_mixed_neg {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hu₄ : u ≤ 4) (hd : 6 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) v < 0 := by
  let h : ℝ := 3/(p : ℝ)
  let c := (3+h)*(3+2*h)/2
  let scale : ℝ := h*Real.sqrt (((p+2).choose 2 : ℝ)/(p+1))/(2*c)
  let d := v-u
  let z := upperTailRadicalRoot h
  let T := deriv z
  let rho := fun s ↦ deriv T s / T s
  let P := radicalLeftFactor p
  let Q := radicalUpperFactor p h
  let J := radicalGapFactor h
  let L := upperTailSlope h
  let j : ℝ → ℝ := fun s ↦ 3/2-L s
  let D : ℝ → ℝ := fun y ↦ z y-z (y-u)
  let M := T v-T d
  let q := L d*(h+L d)
  let C : ℝ → ℝ := fun s ↦ compositionMoment p 0 (-s)
  let α := 1/2-(deriv C u/C u)/2
  let b := 1+2/(Real.exp u-1)-(deriv C u/C u)/2
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hp₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁
  have hdv : d < v := by dsimp [d]; linarith
  have hv : 1 ≤ v := by linarith
  have hd₀ : 0 < d := by linarith
  have hv₀ : 0 < v := by linarith
  have hvdu : v = d+u := by dsimp [d]; ring
  have hvd : v-d = u := by dsimp [d]; ring
  have hscale : 0 < scale := by
    have hN : 0 < ((p+2).choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ p+2 by omega)
    dsimp [scale, c]
    positivity
  have hz (s : ℝ) (hs : 0 < s) : HasDerivAt z (T s) s :=
    (hasDerivAt_upperTailRadicalRoot hh hs).differentiableAt.hasDerivAt
  obtain ⟨hP, hPd⟩ := radicalLeftFactor_jet hp₀ hu
  obtain ⟨hQ, β, hβ, hQd⟩ := radicalUpperFactor_jet hp₀ hv
  obtain ⟨hJ, hJd⟩ := radicalGapFactor_jet hh hd₀
  change HasDerivAt P (P u*α) u at hPd
  change HasDerivAt Q (Q v*β) v at hQd
  change HasDerivAt J (J d*j d) d at hJd
  obtain ⟨hT, hTd, _, _, _, _, _⟩ := separatedGap_radical_logDeriv_bounds hh hhmax hd
  obtain ⟨hD, hM, hc, hRlower, hRupper⟩ :=
    separatedGap_radical_dividedDifference_bounds hh hhmax hd hdv
  change 0 < D v at hD
  change M/D v ≤ -(47/30 : ℝ) at hM
  change rho d - M/D v ≤ (89/25)*(v-d)/(d*v) at hc
  change (47/30)/(1-Real.exp (-((47/30)*(v-d)))) ≤ T d/D v at hRlower
  change T d/D v ≤ 1/(v-d)+21/10 at hRupper
  rw [hvd] at hc hRlower hRupper
  let R := T d/D v
  let U := α-j d+2*R
  let V := β+j d+2*(M/D v)
  have hL := (upperTailSlope_bounds hh hd₀).1
  have hj : j d ≤ 3/2 := by dsimp [j]; linarith only [hL]
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 1/4 ≤ b := upperTail_marginal_scale hp₀ hu
  have hbdef : b = α + 1/2 + 2/(Real.exp u-1) := by dsimp [b, α]; ring
  have hU : 49/60 ≤ U := radical_left_slope_lower hu hRlower hj hb hbdef
  have hV : V ≤ -(49/30 : ℝ) := by dsimp [V]; linarith only [hβ, hj, hM]
  have hUV : U*V ≤ (49/60)*(-(49/30)) := calc
    _ ≤ U * (-(49/30 : ℝ)) :=
      mul_le_mul_of_nonneg_left hV (by linarith only [hU])
    _ ≤ _ := mul_le_mul_of_nonpos_right hU (by norm_num)
  have herror : 2*R*(rho d-M/D v) ≤ 4183/3750 :=
    radical_curvature_error hu hu₄ hd hvdu (div_nonneg hT.le hD.le) hRupper hc
  have hsign : U*V-q+2*R*(rho d-M/D v) < 0 := by
    linarith only [hUV, hq, herror]
  have hformula (y : ℝ) (hy : 0 < y-u) :
      deriv (fun x ↦ separatedGapRadicalContribution p x y) u =
        scale*(P u*Q y*J (y-u)*
          ((D y)^2*(α-j (y-u))+2*D y*T (y-u))) := by
    have hynear : ∀ᶠ x in 𝓝 u, 0 < y-x :=
      ((continuous_const.sub continuous_id).continuousAt :
        ContinuousAt (fun x : ℝ ↦ y-x) u).eventually (eventually_gt_nhds hy)
    have heq : (fun x ↦ separatedGapRadicalContribution p x y) =ᶠ[𝓝 u]
        (fun x ↦ scale*radicalFactorization p h x y) := by
      filter_upwards [eventually_gt_nhds hu, hynear] with x hx hxy
      exact separatedGapRadicalContribution_eq hp₀ hx hxy
    have hd' : HasDerivAt (fun x : ℝ ↦ y-x) (-1) u := by
      simpa only [zero_sub] using (hasDerivAt_id' u).const_sub y
    have hJ' := ((radicalGapFactor_jet hh hy).2).comp u hd'
    change HasDerivAt (fun x ↦ J (y-x)) ((J (y-u)*j (y-u))*(-1)) u at hJ'
    have hZ' := ((hz (y-u) hy).comp u hd').const_sub (z y)
    change HasDerivAt (fun x ↦ z y-z (y-x)) (-(T (y-u)*(-1))) u at hZ'
    have hder := (((hPd.mul_const (Q y)).mul hJ').mul (hZ'.pow 2)).const_mul scale
    change HasDerivAt (fun x ↦ scale*radicalFactorization p h x y) _ u at hder
    rw [heq.deriv_eq, hder.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.mul_apply, Pi.pow_apply]
    change _ = scale*(P u*Q y*J (y-u)*((z y-z (y-u))^2*(α-j (y-u))+
      2*(z y-z (y-u))*T (y-u)))
    ring
  have hlocal : (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) =ᶠ[𝓝 v]
      (fun y ↦ scale*(P u*Q y*J (y-u)*((D y)^2*(α-j (y-u))+2*D y*T (y-u)))) := by
    have hpos : ∀ᶠ y in 𝓝 v, 0 < y-u :=
      ((continuous_id.sub continuous_const).continuousAt :
        ContinuousAt (fun y : ℝ ↦ y-u) v).eventually (eventually_gt_nhds hd₀)
    exact hpos.mono hformula
  have hg : HasDerivAt (fun y : ℝ ↦ y-u) 1 v := (hasDerivAt_id' v).sub_const u
  have hD' : HasDerivAt D M v := by
    have hdif := (hz v hv₀).sub ((hz d hd₀).comp v hg)
    change HasDerivAt D (T v-T d*1) v at hdif
    simpa only [M, mul_one] using hdif
  have hj' : HasDerivAt (fun y ↦ α-j (y-u)) (-q) v := by
    have hl := ((hasDerivAt_upperTailSlope hh hd₀).comp v hg).const_sub (3/2 : ℝ)
    have hdif := hl.const_sub α
    change HasDerivAt (fun y ↦ α-j (y-u)) (-(-(-q*1))) v at hdif
    simpa only [mul_one, neg_neg] using hdif
  have hT' : HasDerivAt (fun y ↦ T (y-u)) (T d*rho d) v := by
    have ht := hTd.hasDerivAt.congr_deriv (show deriv T d = T d*rho d by
      dsimp [rho]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hT.ne'])
    have hdif := ht.comp v hg
    change HasDerivAt (fun y ↦ T (y-u)) (T d*rho d*1) v at hdif
    simpa only [mul_one] using hdif
  have hJ' := hJd.comp v hg
  change HasDerivAt (fun y ↦ J (y-u)) (J d*j d*1) v at hJ'
  have hleft := (hQd.const_mul (P u)).mul hJ'
  have hright := ((hD'.pow 2).mul hj').add ((hD'.const_mul 2).mul hT')
  have hder := (hleft.mul hright).const_mul scale
  change HasDerivAt (fun y ↦ scale*(P u*Q y*J (y-u)*
    ((D y)^2*(α-j (y-u))+2*D y*T (y-u)))) _ v at hder
  rw [hlocal.deriv_eq, hder.deriv]
  calc
    _ = scale*(P u*Q v*J d*(D v)^2)*(U*V-q+2*R*(rho d-M/D v)) := by
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.mul_apply, Pi.add_apply,
        Pi.pow_apply]
      change scale*((P u*(Q v*β)*J d + P u*Q v*(J d*j d))*
        ((D v)^2*(α-j d)+2*D v*T d) + P u*Q v*J d*
        (2*D v*M*(α-j d)+(D v)^2*(-q)+(2*M*T d+2*D v*(T d*rho d)))) = _
      dsimp only [U, V, R]
      field_simp [hD.ne']
      ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos hscale
      (mul_pos (mul_pos (mul_pos hP hQ) hJ) (sq_pos_of_pos hD))) hsign

#print axioms separatedGap_radical_logDeriv_bounds
#print axioms separatedGap_radical_dividedDifference_bounds
#print axioms separatedGap_radical_mixed_neg

end RefinedBMV.PositiveCenter
