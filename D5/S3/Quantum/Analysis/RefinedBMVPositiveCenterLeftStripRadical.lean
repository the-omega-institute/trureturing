/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripRadical
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit smallness of the BMV lower-collision root-difference residual. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripProfile

/-! # The lower-collision radical residual on the separated strip -/

noncomputable section

namespace RefinedBMV.PositiveCenter

theorem abs_add_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x+y| ≤ X+Y := (abs_add_le x y).trans (add_le_add hx hy)

theorem abs_sub_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x-y| ≤ X+Y := (abs_sub x y).trans (add_le_add hx hy)

theorem abs_mul_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x*y| ≤ X*Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_sq_bound {x X : ℝ} (hx : |x| ≤ X) : |x^2| ≤ X^2 := by
  simpa only [pow_two] using abs_mul_bound hx hx

private theorem abs_half_bound {x X : ℝ} (hx : |x| ≤ X) : |x/2| ≤ X/2 := by
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right hx (by norm_num)

theorem leftStrip_slope_bounds {h t : ℝ} (hh : 0 < h) (ht : 6 ≤ t) :
    0 < upperTailSlope h t ∧ upperTailSlope h t ≤ 1/6 ∧
      5/6 ≤ profileSlope h t ∧ profileSlope h t ≤ 1 ∧
      0 ≤ profileCurvature h t ∧ profileCurvature h t ≤ 1/36 := by
  have ht₀ : 0 < t := by linarith
  obtain ⟨hLpos, hLmax, _, hqmax, _, _⟩ := upperTailSlope_bounds hh ht₀
  rw [(hasDerivAt_upperTailSlope hh ht₀).deriv, neg_neg] at hqmax
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) ht
  have hL := hLmax.trans hInv
  have hq : 1/t^2 ≤ (1 : ℝ)/36 := by
    simpa only [one_div_pow, show (1/6 : ℝ)^2 = 1/36 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1/t) hInv 2
  exact ⟨hLpos, hL, by dsimp [profileSlope]; linarith, by dsimp [profileSlope]; linarith,
    mul_nonneg hLpos.le (add_nonneg hh.le hLpos.le), hqmax.trans hq⟩

/-- The radical correction spends less than (47/450) of the negative
geometric margin in the weighted third derivative. -/
theorem leftStrip_radical_mixed_lt {h a v γ : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ha : 0 ≤ a) (hamax : a ≤ 1/2)
    (hgap : 6 ≤ v-a) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1) :
    |deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) x) a) v -
        γ * deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t v) x) a| < 47/450 := by
  let s := v-a
  let B := ((3+h)*(3+2*h)/2) * (upperTailGap h s)^2 * Real.exp (-(2*s))
  let b : ℝ → ℝ := fun x ↦ Real.sqrt (1 - upperTailLambda h x)
  let x := deriv b s
  let y := deriv (deriv b) s
  let z := deriv (deriv (deriv b)) s
  let δ := b v-b s
  let δ₁ := deriv b v-deriv b s
  let L := profileSlope h s
  let q := profileCurvature h s
  let q₁ := -q*(h+2*upperTailSlope h s)
  let W := leftStripWeight h a v
  let M := x^2-δ*y-2*L*δ*x+(L^2+q)*δ^2/2
  let M₁ := 2*x*y-δ₁*y-δ*z-2*q*δ*x-2*L*(δ₁*x+δ*y)+
    (2*L*q+q₁)*δ^2/2+(L^2+q)*δ*δ₁
  have hsv : s ≤ v := sub_le_self v ha
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBmax : B < 1/750 := (separated_radical_lower hh hhmax hgap).1
  obtain ⟨hx, hy, hz⟩ := separated_radical_derivative_bounds hh hhmax hgap
  change |x| ≤ (13/10)*B at hx
  change |y| ≤ (33/10)*B at hy
  change |z| ≤ (83/10)*B at hz
  obtain ⟨hd, hd₁, _⟩ := separated_radical_difference_bounds hh hhmax hgap hsv
  have hδ : |δ| ≤ (13/20)*B := by
    change |δ| ≤ (13/10)*B*(v-s) at hd
    rw [show v-s = a by dsimp [s]; ring] at hd
    exact hd.trans ((mul_le_mul_of_nonneg_left hamax (by positivity)).trans_eq (by ring))
  have hδ₁ : |δ₁| ≤ (33/20)*B := by
    change |δ₁| ≤ (33/10)*B*(v-s) at hd₁
    rw [show v-s = a by dsimp [s]; ring] at hd₁
    exact hd₁.trans ((mul_le_mul_of_nonneg_left hamax (by positivity)).trans_eq (by ring))
  obtain ⟨hL₀, hLmax, hLlo, hLhi, hq₀, hqhi⟩ := leftStrip_slope_bounds hh hgap
  obtain ⟨_, _, hVlo, hVhi, _, _⟩ := leftStrip_slope_bounds hh (hgap.trans hsv)
  have hL : |L| ≤ 1 := abs_le.mpr ⟨by change 5/6 ≤ L at hLlo; linarith, hLhi⟩
  have hq : |q| ≤ 1/36 := (abs_of_nonneg hq₀).trans_le hqhi
  have hC : |profileSlope h v+L-γ| ≤ 2 := by
    change 5/6 ≤ L at hLlo
    change L ≤ 1 at hLhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hq₁ : |q₁| ≤ 1/50 := by
    change |(-q)*(h+2*upperTailSlope h s)| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h+2*upperTailSlope h s)]
    have htop : h+2*upperTailSlope h s ≤ 3/11+1/3 := by linarith
    exact (mul_le_mul hq htop (by positivity) (by norm_num)).trans (by norm_num)
  have h2 : |(2 : ℝ)| ≤ 2 := by norm_num
  have hLq : |L^2+q| ≤ 37/36 :=
    (abs_add_bound (abs_sq_bound hL) hq).trans (by norm_num)
  have hLq₁ : |2*L*q+q₁| ≤ 1/10 :=
    (abs_add_bound (abs_mul_bound (abs_mul_bound h2 hL) hq) hq₁).trans (by norm_num)
  have hM : |M| ≤ 6*B^2 := by
    unfold M
    have hraw := abs_add_bound
      (abs_sub_bound (abs_sub_bound (abs_sq_bound hx) (abs_mul_bound hδ hy))
        (abs_mul_bound (abs_mul_bound (abs_mul_bound h2 hL) hδ) hx))
      (abs_half_bound (abs_mul_bound hLq (abs_sq_bound hδ)))
    exact hraw.trans (by nlinarith only [sq_nonneg B])
  have hM₁ : |M₁| ≤ 30*B^2 := by
    unfold M₁
    have hraw := abs_add_bound
      (abs_add_bound
        (abs_sub_bound
          (abs_sub_bound
            (abs_sub_bound
              (abs_sub_bound (abs_mul_bound (abs_mul_bound h2 hx) hy) (abs_mul_bound hδ₁ hy))
              (abs_mul_bound hδ hz))
            (abs_mul_bound (abs_mul_bound (abs_mul_bound h2 hq) hδ) hx))
          (abs_mul_bound (abs_mul_bound h2 hL)
            (abs_add_bound (abs_mul_bound hδ₁ hx) (abs_mul_bound hδ hy))))
        (abs_half_bound (abs_mul_bound hLq₁ (abs_sq_bound hδ))))
      (abs_mul_bound (abs_mul_bound hLq hδ) hδ₁)
    exact hraw.trans (by nlinarith only [sq_nonneg B])
  have hW : 0 ≤ W := by dsimp [W, leftStripWeight]; positivity
  have hWB : W*B ≤ 5/3 := leftStrip_weight_mul_square_le hh ha hamax hgap
  rw [leftStrip_radical_mixed_formula hh hhmax ha hgap]
  change |W*((profileSlope h v+L-γ)*M+M₁)| < _
  calc
    _ ≤ W*(2*(6*B^2)+30*B^2) :=
      abs_mul_bound ((abs_of_nonneg hW).le) (abs_add_bound (abs_mul_bound hC hM) hM₁)
    _ = 42*(W*B)*B := by ring
    _ ≤ 42*(5/3)*(1/750) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hWB (by norm_num)) hBmax.le hB (by norm_num)
    _ < _ := by norm_num

#print axioms leftStrip_radical_mixed_lt

open Filter Set
open scoped Topology

private theorem profile_bounds_three {h t : ℝ} (hh : 0 < h) (ht : 3 ≤ t) :
    0 < upperTailSlope h t ∧ upperTailSlope h t ≤ 1/3 ∧
      2/3 ≤ profileSlope h t ∧ profileSlope h t ≤ 1 ∧
      0 ≤ profileCurvature h t ∧ profileCurvature h t ≤ 1/9 := by
  have ht₀ : 0 < t := by linarith
  obtain ⟨hH₀, hH, hq₀, hq, _, _⟩ := upperTailSlope_bounds hh ht₀
  rw [(hasDerivAt_upperTailSlope hh ht₀).deriv, neg_neg] at hq₀ hq
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) ht
  have hH' := hH.trans hi
  have hq' : 1/t^2 ≤ (1 : ℝ)/9 := by
    simpa only [one_div_pow, show (1/3 : ℝ)^2 = 1/9 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1/t) hi 2
  exact ⟨hH₀, hH', by unfold profileSlope; linarith, by unfold profileSlope; linarith,
    hq₀, hq.trans hq'⟩

private theorem exp_neg_three_le {t : ℝ} (ht : 3 ≤ t) : Real.exp (-t) ≤ 1/20 := by
  have he : (20 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    have ho : (2718/1000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    exact (by norm_num : (20 : ℝ) < (2718/1000)^3).trans
      (pow_lt_pow_left₀ ho (by norm_num) (by decide))
  calc
    Real.exp (-t) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1/20 := by rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) he.le

private theorem mul_exp_neg_le_three_twentieths {t : ℝ} (ht : 3 ≤ t) :
    t * Real.exp (-t) ≤ 3/20 := by
  have h : t ≤ 3*Real.exp (t-3) := by linarith [Real.add_one_le_exp (t-3)]
  have he : Real.exp (t-3)*Real.exp (-t) = Real.exp (-3) := by
    rw [← Real.exp_add, show t-3 + -t = -3 by ring]
  calc
    _ ≤ 3*Real.exp (t-3)*Real.exp (-t) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 3*Real.exp (-3) := by rw [mul_assoc, he]
    _ ≤ 3/20 := by linarith [exp_neg_three_le (t := 3) le_rfl]

private theorem gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) : 0 < upperTailGap h t :=
  div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))) hh

private theorem radical_size_three {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (ht : 3 ≤ t) :
    separatedSquare h t ≤ 27/200 ∧ (6 : ℝ)/7 ≤ 1 - upperTailLambda h t := by
  let F := upperTailGap h t
  let e := Real.exp (-t)
  let g := 3+h
  let c := g*(3+2*h)/2
  have ht₀ : 0 < t := by linarith
  have hF := (gap_pos hh ht₀).le
  have he := (Real.exp_pos (-t)).le
  have hemax : e ≤ 1/20 := exp_neg_three_le ht
  have hFe : F*e ≤ 3/20 := (mul_le_mul_of_nonneg_right (upperTailGap_le hh) he).trans
    (mul_exp_neg_le_three_twentieths ht)
  have hg : g ≤ 10/3 := by dsimp [g]; linarith
  have hc : c ≤ 6 := by
    have h₁ : g ≤ 36/11 := by dsimp [g]; linarith
    have h₂ : 3+2*h ≤ 39/11 := by linarith
    have hm := mul_le_mul h₁ h₂ (by positivity : 0 ≤ 3+2*h) (by norm_num)
    dsimp [c]
    linarith
  have he₂ : Real.exp (-(2*t)) = e^2 := by
    dsimp only [e]; rw [pow_two, ← Real.exp_add]; congr 1; ring
  have he₃ : Real.exp (-(g*t)) ≤ e^3 := by
    rw [show e^3 = Real.exp (-(3*t)) by
      dsimp only [e]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    exact Real.exp_le_exp.mpr (by dsimp [g]; nlinarith [mul_nonneg hh.le ht₀.le])
  have hB : separatedSquare h t ≤ 27/200 := by
    change c*F^2*Real.exp (-(2*t)) ≤ _
    rw [he₂, show c*F^2*e^2 = c*(F*e)^2 by ring]
    exact (mul_le_mul hc (pow_le_pow_left₀ (mul_nonneg hF he) hFe 2)
      (sq_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hA : (1+g*F)*Real.exp (-(g*t)) ≤ 11/8000 := by
    have hg₀ : 0 ≤ g := by dsimp [g]; positivity
    calc
      _ ≤ (1+g*F)*e^3 := mul_le_mul_of_nonneg_left he₃ (by positivity)
      _ = e^3 + (g*(F*e))*e^2 := by ring
      _ ≤ (1/20 : ℝ)^3 + ((10/3)*(3/20))*(1/20)^2 := by
        exact add_le_add (pow_le_pow_left₀ he hemax 3)
          (mul_le_mul (mul_le_mul hg hFe (mul_nonneg hF he) (by norm_num))
            (pow_le_pow_left₀ he hemax 2) (by positivity) (by norm_num))
      _ = _ := by norm_num
  refine ⟨hB, ?_⟩
  change (6 : ℝ)/7 ≤ 1 - ((1+g*F)*Real.exp (-(g*t)) + separatedSquare h t)
  linarith

theorem leftStrip_radical_radicand_pos {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (ht : 3 ≤ t) : 0 < 1 - upperTailLambda h t :=
  (by norm_num : (0 : ℝ) < 6/7).trans_le (radical_size_three hh hhmax ht).2

private def radicalRepeat (h t : ℝ) : ℝ :=
  Real.exp (-((1+h)*t)) / upperTailGap h t

private def radicalRate (h t : ℝ) : ℝ := profileSlope h t + radicalRepeat h t

private def radicalRateFirst (h t : ℝ) : ℝ :=
  profileCurvature h t - (1+h+upperTailSlope h t)*radicalRepeat h t

private def radicalRoot (h t : ℝ) : ℝ := Real.sqrt (1 - upperTailLambda h t)

private def radicalError (h t : ℝ) : ℝ :=
  radicalRateFirst h t / radicalRate h t -
    separatedSquare h t * radicalRate h t / (1 - upperTailLambda h t)

private theorem gap_slope_eq {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    Real.exp (-(h*t)) = upperTailSlope h t * upperTailGap h t := by
  have he := upperTailGap_logDeriv hh ht
  rw [(hasDerivAt_upperTailGap hh).deriv] at he
  exact (div_eq_iff (gap_pos hh ht).ne').mp he

private theorem hasDerivAt_radicalRepeat {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (radicalRepeat h) (-(1+h+upperTailSlope h t)*radicalRepeat h t) t := by
  have hd := (((hasDerivAt_id' t).const_mul (1+h)).neg).exp
  have hd' : HasDerivAt (fun x : ℝ ↦ Real.exp (-((1+h)*x)))
      (-(1+h)*Real.exp (-((1+h)*t))) t := by
    exact hd.congr_deriv (by simp only [Pi.neg_apply, mul_one]; ring)
  have hf := hd'.fun_div (hasDerivAt_upperTailGap hh) (gap_pos hh ht).ne'
  apply hf.congr_deriv
  rw [gap_slope_eq hh ht]
  unfold radicalRepeat
  field_simp [(gap_pos hh ht).ne']
  <;> ring

private theorem radicalRepeat_bound {h t : ℝ} (hh : 0 < h) (ht : 3 ≤ t) :
    0 ≤ radicalRepeat h t ∧ radicalRepeat h t ≤ (3/20)*profileCurvature h t := by
  have ht₀ : 0 < t := by linarith
  let F := upperTailGap h t
  let H := upperTailSlope h t
  have hF := gap_pos hh ht₀
  have hHF : (h+H)*F = 1 := by
    have hf : h*F = 1-Real.exp (-(h*t)) := by
      dsimp [F, upperTailGap]; field_simp [hh.ne']
    linarith only [hf, gap_slope_eq hh ht₀]
  have hEq : radicalRepeat h t = profileCurvature h t * (F*Real.exp (-t)) := by
    unfold radicalRepeat
    rw [show -((1+h)*t) = -(h*t) + -t by ring, Real.exp_add, gap_slope_eq hh ht₀]
    change H*F*Real.exp (-t)/F = H*(h+H)*(F*Real.exp (-t))
    rw [mul_assoc H (h+H), ← mul_assoc (h+H) F, hHF, one_mul]
    rw [mul_right_comm H F, mul_div_cancel_right₀ _ hF.ne']
  rw [hEq]
  have hq := (profile_bounds_three hh ht).2.2.2.2.1
  exact ⟨mul_nonneg hq (mul_nonneg hF.le (Real.exp_pos _).le),
    (mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (upperTailGap_le hh) (Real.exp_pos _).le).trans
        (mul_exp_neg_le_three_twentieths ht)) hq).trans_eq (mul_comm _ _)⟩

private theorem hasDerivAt_radicalRate {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (radicalRate h) (radicalRateFirst h t) t := by
  have hd := (hasDerivAt_profileSlope hh ht).add (hasDerivAt_radicalRepeat hh ht)
  change HasDerivAt (radicalRate h) _ t at hd
  simpa only [radicalRateFirst, neg_mul, sub_eq_add_neg] using hd

private theorem hasDerivAt_radicalRadicand {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (fun x ↦ 1 - upperTailLambda h x)
      (2 * separatedSquare h t * radicalRate h t) t := by
  have hd := (hasDerivAt_upperTailLambda (t := t) hh).const_sub 1
  apply hd.congr_deriv
  have hF := gap_pos hh ht
  have hf : h*upperTailGap h t = 1-Real.exp (-(h*t)) := by
    unfold upperTailGap; field_simp [hh.ne']
  have he := gap_slope_eq hh ht
  have hcore : (1+h)*upperTailGap h t - 1 =
      upperTailGap h t * (1-upperTailSlope h t) := by nlinarith only [hf, he]
  rw [hcore]
  unfold separatedSquare radicalRate radicalRepeat profileSlope
  field_simp [hF.ne']
  <;> ring

private theorem hasDerivAt_radicalRoot {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hS : 0 < 1 - upperTailLambda h t) :
    HasDerivAt (radicalRoot h) (separatedSquare h t * radicalRate h t / radicalRoot h t) t := by
  have hf := (hasDerivAt_radicalRadicand hh ht).sqrt hS.ne'
  have hb := (Real.sqrt_pos.mpr hS).ne'
  apply hf.congr_deriv
  change _ = separatedSquare h t * radicalRate h t / Real.sqrt (1 - upperTailLambda h t)
  field_simp [hb]
  <;> ring

private theorem hasDerivAt_radicalRoot_first {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hS : 0 < 1 - upperTailLambda h t) (hw : 0 < radicalRate h t) :
    HasDerivAt (deriv (radicalRoot h))
      ((radicalError h t - 2*profileSlope h t)*deriv (radicalRoot h) t) t := by
  have hb := hasDerivAt_radicalRoot hh ht hS
  have hb₀ : 0 < radicalRoot h t := Real.sqrt_pos.mpr hS
  have hbSq : radicalRoot h t^2 = 1 - upperTailLambda h t := Real.sq_sqrt hS.le
  have heq : deriv (radicalRoot h) =ᶠ[𝓝 t]
      fun x ↦ separatedSquare h x * radicalRate h x / radicalRoot h x := by
    filter_upwards [eventually_gt_nhds ht,
      (hasDerivAt_radicalRadicand hh ht).continuousAt.eventually (eventually_gt_nhds hS)]
      with x hx hSx using (hasDerivAt_radicalRoot hh hx hSx).deriv
  have hd := ((hasDerivAt_separatedSquare hh ht).mul (hasDerivAt_radicalRate hh ht)).fun_div hb hb₀.ne'
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  rw [hb.deriv]
  unfold radicalError
  rw [← hbSq]
  simp only [Pi.mul_apply]
  field_simp [hw.ne', hb₀.ne']
  <;> ring

private theorem radical_rate_bounds {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (ht : 3 ≤ t) :
    2/3 ≤ radicalRate h t ∧ radicalRate h t ≤ 61/60 ∧
      0 ≤ radicalRateFirst h t ∧ radicalRateFirst h t ≤ profileCurvature h t := by
  obtain ⟨hH₀, hH, hL, hLmax, hq₀, hq⟩ := profile_bounds_three hh ht
  obtain ⟨hr₀, hr⟩ := radicalRepeat_bound hh ht
  have hm := mul_le_mul (show 1+h+upperTailSlope h t ≤ 53/33 by linarith) hr hr₀
    (by norm_num : (0 : ℝ) ≤ 53/33)
  unfold radicalRate radicalRateFirst
  exact ⟨by linarith, by linarith, by linarith,
    sub_le_self _ (mul_nonneg (by positivity) hr₀)⟩

private theorem radical_error_bounds {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (ht : 3 ≤ t) :
    -(1/6 : ℝ) ≤ radicalError h t ∧ radicalError h t ≤ 1/6 ∧
      -(1/5 : ℝ) ≤ deriv (radicalError h) t := by
  let B := separatedSquare h t
  let S := 1 - upperTailLambda h t
  let W := radicalRate h t
  let W₁ := radicalRateFirst h t
  let H := upperTailSlope h t
  let L := profileSlope h t
  let q := profileCurvature h t
  let r := radicalRepeat h t
  let q₁ := -(q*(h+2*H))
  let W₂ := q₁ + (q+(1+h+H)^2)*r
  have ht₀ : 0 < t := by linarith
  obtain ⟨hH₀, hH, hL, hLmax, hq₀, hq⟩ := profile_bounds_three hh ht
  obtain ⟨hB, hS⟩ := radical_size_three hh hhmax ht
  obtain ⟨hW, hWmax, hW₁₀, hW₁max⟩ := radical_rate_bounds hh hhmax ht
  change 2/3 ≤ W at hW
  change W ≤ 61/60 at hWmax
  change 0 ≤ W₁ at hW₁₀
  change W₁ ≤ q at hW₁max
  change separatedSquare h t ≤ 27/200 at hB
  have hS₀ : 0 < S := (by norm_num : (0 : ℝ) < 6/7).trans_le hS
  have hW₀ : 0 < W := (by norm_num : (0 : ℝ) < 2/3).trans_le hW
  have hB₀ : 0 ≤ B := by dsimp [B, separatedSquare]; positivity
  have hdiv₀ : 0 ≤ W₁/W := div_nonneg hW₁₀ hW₀.le
  have hdiv : W₁/W ≤ 1/6 := (div_le_iff₀ hW₀).mpr (by linarith only [hW₁max, hq, hW])
  have hprod₀ : 0 ≤ B*W/S := div_nonneg (mul_nonneg hB₀ hW₀.le) hS₀.le
  have hprod : B*W/S ≤ 1/6 := by
    apply (div_le_iff₀ hS₀).mpr
    have hBW := mul_le_mul hB hWmax hW₀.le (by norm_num)
    linarith only [hBW, hS]
  have hW₂ : HasDerivAt (radicalRateFirst h) W₂ t := by
    have hd := (hasDerivAt_profileCurvature hh ht₀).sub
      (((hasDerivAt_upperTailSlope hh ht₀).const_add (1+h)).mul (hasDerivAt_radicalRepeat hh ht₀))
    apply hd.congr_deriv
    simp only [W₂, q₁, H, q, r, profileCurvature]
    ring
  have hNum : B*(W₁-2*L*W) ≤ 0 := by
    have hm := mul_le_mul hL hW (by norm_num) (by linarith)
    apply mul_nonpos_of_nonneg_of_nonpos hB₀
    linarith only [hm, hW₁max, hq]
  have hsub : ((B*(W₁-2*L*W))*S - (B*W)*(2*B*W))/S^2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos_of_le ((mul_nonpos_of_nonpos_of_nonneg hNum hS₀.le).trans
        (by positivity))) (sq_nonneg S)
  have hfirst : -(31/198 : ℝ) ≤ W₂/W := by
    apply (le_div_iff₀ hW₀).mpr
    have hqe : q*(h+2*H) ≤ (1/9 : ℝ)*(31/33) :=
      mul_le_mul hq (by dsimp [H]; linarith) (by dsimp [H]; positivity) (by norm_num)
    have hp : 0 ≤ (q+(1+h+H)^2)*r :=
      mul_nonneg (add_nonneg hq₀ (sq_nonneg _)) (radicalRepeat_bound hh ht).1
    dsimp only [W₂, q₁]
    linarith only [hqe, hp, hW]
  have hDerivative : deriv (radicalError h) t =
      W₂/W - (W₁/W)^2 -
        ((B*(W₁-2*L*W))*S - (B*W)*(2*B*W))/S^2 := by
    have hd := (hW₂.fun_div (hasDerivAt_radicalRate hh ht₀) hW₀.ne').sub
      (((hasDerivAt_separatedSquare hh ht₀).mul (hasDerivAt_radicalRate hh ht₀)).fun_div
        (hasDerivAt_radicalRadicand hh ht₀) hS₀.ne')
    change HasDerivAt (radicalError h) _ t at hd
    rw [hd.deriv]
    change (W₂*W-W₁*W₁)/W^2 -
      (((-2*L*B)*W+B*W₁)*S-B*W*(2*B*W))/S^2 = _
    field_simp [hW₀.ne', hS₀.ne']
    <;> ring
  change -(1/6 : ℝ) ≤ W₁/W - B*W/S ∧ W₁/W - B*W/S ≤ 1/6 ∧ _
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hDerivative]
  have hsquare := pow_le_pow_left₀ hdiv₀ hdiv 2
  linarith only [hfirst, hsquare, hsub]

/-- The correlated root-difference term gives a strictly favorable contribution
on the left strip as soon as the gap is at least three. -/
theorem leftStrip_radical_correlated_le {h a v γ : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3/11) (ha : 0 ≤ a) (hamax : a ≤ 1/2)
    (hgap : 3 ≤ v-a) (hγ : 5/12 ≤ γ) (hγmax : γ ≤ 1) :
    let b (t : ℝ) := Real.sqrt (1 - upperTailLambda h t)
    let bound := -(167/180 : ℝ) * leftStripWeight h a v * (deriv b (v-a))^2
    (deriv (fun y ↦ deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t y) x) a) v -
      γ * deriv (fun x ↦ deriv (fun t ↦ leftStripRadicalTerm h t v) x) a ≤ bound) ∧
      bound < 0 := by
  let s := v-a
  let b := radicalRoot h
  let L := profileSlope h s
  let q := profileCurvature h s
  let q₁ := -q*(h+2*upperTailSlope h s)
  let ε := radicalError h s
  let ε₁ := deriv (radicalError h) s
  let m (t : ℝ) := 2*profileSlope h t - radicalError h t
  let x := deriv b s
  let Δ := b v-b s
  let Δ₁ := deriv b v - x
  let ζ := profileSlope h v + L - γ
  let M := x^2 - Δ*deriv (deriv b) s - 2*L*Δ*x + (L^2+q)*Δ^2/2
  let M₁ := 2*x*deriv (deriv b) s - Δ₁*deriv (deriv b) s -
    Δ*deriv (deriv (deriv b)) s - 2*q*Δ*x -
    2*L*(Δ₁*x+Δ*deriv (deriv b) s) + (2*L*q+q₁)*Δ^2/2 + (L^2+q)*Δ*Δ₁
  have hs : 0 < s := by linarith
  have hsv : s ≤ v := sub_le_self _ ha
  have hv : 0 < v := hs.trans_le hsv
  have hv₃ : 3 ≤ v := hgap.trans hsv
  have hS {t : ℝ} (ht : 3 ≤ t) : 0 < 1-upperTailLambda h t :=
    leftStrip_radical_radicand_pos hh hhmax ht
  have hw {t : ℝ} (ht : 3 ≤ t) : 0 < radicalRate h t :=
    (by norm_num : (0 : ℝ) < 2/3).trans_le (radical_rate_bounds hh hhmax ht).1
  have hb {t : ℝ} (ht : 3 ≤ t) : HasDerivAt b (deriv b t) t :=
    (hasDerivAt_radicalRoot hh (by linarith) (hS ht)).differentiableAt.hasDerivAt
  have hbpos {t : ℝ} (ht : 3 ≤ t) : 0 < deriv b t := by
    have hF := gap_pos hh (show 0 < t by linarith)
    have hb₀ : 0 < radicalRoot h t := Real.sqrt_pos.mpr (hS ht)
    rw [(hasDerivAt_radicalRoot hh (by linarith) (hS ht)).deriv]
    exact div_pos (mul_pos (by unfold separatedSquare; positivity) (hw ht)) hb₀
  have hb₁ {t : ℝ} (ht : 3 ≤ t) : HasDerivAt (deriv b) (-m t*deriv b t) t := by
    convert hasDerivAt_radicalRoot_first hh (show 0 < t by linarith) (hS ht) (hw ht) using 1
    dsimp [m, b]; ring
  have hm {t : ℝ} (ht : 3 ≤ t) : 7/6 ≤ m t ∧ m t ≤ 13/6 := by
    obtain ⟨_, _, hL, hLmax, _, _⟩ := profile_bounds_three hh ht
    obtain ⟨he, hemax, _⟩ := radical_error_bounds hh hhmax ht
    unfold m
    exact ⟨by linarith, by linarith⟩
  have hb₂ : deriv (deriv b) s = -m s*x := (hb₁ hgap).deriv
  have hb₃ : deriv (deriv (deriv b)) s =
      (ε₁-2*q)*x + (m s)^2*x := by
    have hws : 0 < radicalRate h s := hw hgap
    have hnear : ∀ᶠ t in 𝓝 s, 0 < 1-upperTailLambda h t :=
      (hasDerivAt_radicalRadicand hh hs).continuousAt.eventually (eventually_gt_nhds (hS hgap))
    have hwn : ∀ᶠ t in 𝓝 s, 0 < radicalRate h t :=
      (hasDerivAt_radicalRate hh hs).continuousAt.eventually (eventually_gt_nhds hws)
    have heq : deriv (deriv b) =ᶠ[𝓝 s] fun t ↦
        (radicalError h t - 2*profileSlope h t)*deriv b t := by
      filter_upwards [eventually_gt_nhds hs, hnear, hwn] with t ht hSt hwt
      exact (hasDerivAt_radicalRoot_first hh ht hSt hwt).deriv
    have hr := (hasDerivAt_upperTailSlope hh hs).const_add (1+h)
    have hq' := hasDerivAt_profileCurvature hh hs
    have hw' := hq'.sub (hr.mul (hasDerivAt_radicalRepeat hh hs))
    change HasDerivAt (radicalRateFirst h) _ s at hw'
    have he : DifferentiableAt ℝ (radicalError h) s :=
      (hw'.fun_div (hasDerivAt_radicalRate hh hs) hws.ne' |>.sub
        (((hasDerivAt_separatedSquare hh hs).mul (hasDerivAt_radicalRate hh hs)).fun_div
          (hasDerivAt_radicalRadicand hh hs) (hS hgap).ne')).differentiableAt
    have hd := (he.hasDerivAt.sub ((hasDerivAt_profileSlope hh hs).const_mul 2)).mul
      (hb₁ hgap)
    change HasDerivAt (fun t ↦ (radicalError h t - 2*profileSlope h t)*deriv b t) _ s at hd
    rw [heq.deriv_eq, hd.deriv]
    dsimp [m, ε, ε₁, x, q]
    ring
  have hx : 0 < x := hbpos hgap
  have hsec : 0 ≤ Δ ∧ Δ ≤ x/2 ∧
      ∃ μ : ℝ, 7/6 ≤ μ ∧ μ ≤ 13/6 ∧ Δ₁ = -μ*Δ := by
    rcases hsv.eq_or_lt with hEq | hlt
    · simp [Δ, Δ₁, x, hEq]
      exact ⟨by linarith [hbpos hv₃], 7/6, le_rfl, by norm_num⟩
    have haEq : v-s = a := by dsimp [s]; ring
    have hbc : ContinuousOn b (Icc s v) :=
      fun t ht ↦ (hb (hgap.trans ht.1)).continuousAt.continuousWithinAt
    have hbc₁ : ContinuousOn (deriv b) (Icc s v) :=
      fun t ht ↦ (hb₁ (hgap.trans ht.1)).continuousAt.continuousWithinAt
    have hAnti : AntitoneOn (deriv b) (Icc s v) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hbc₁
      · rw [interior_Icc]
        exact fun t ht ↦ (hb₁ (hgap.trans ht.1.le)).differentiableAt.differentiableWithinAt
      rw [interior_Icc]
      intro t ht
      rw [(hb₁ (hgap.trans ht.1.le)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (by linarith [(hm (hgap.trans ht.1.le)).1]) (hbpos (hgap.trans ht.1.le)).le
    obtain ⟨t, ht, hmean⟩ := exists_hasDerivAt_eq_slope b (deriv b) hlt hbc
      (fun t ht ↦ hb (hgap.trans ht.1.le))
    have hΔ : deriv b t * a = Δ := by
      rw [← haEq]
      exact (eq_div_iff (sub_pos.mpr hlt).ne').mp hmean
    have hslope : deriv b t ≤ x :=
      hAnti ⟨le_rfl, hsv⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le
    have hΔ₀ : 0 ≤ Δ := hΔ ▸ mul_nonneg (hbpos (hgap.trans ht.1.le)).le ha
    have hΔmax : Δ ≤ x/2 := by
      rw [← hΔ]
      exact (mul_le_mul hslope hamax ha hx.le).trans_eq (by ring)
    obtain ⟨c, hc, hcauchy⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun t ↦ -deriv b t) (fun t ↦ m t*deriv b t) hlt hbc₁.neg
      (fun t ht ↦ by
        have hd := (hb₁ (hgap.trans ht.1.le)).neg
        change HasDerivAt (fun r ↦ -deriv b r) _ t at hd
        simpa only [neg_mul, neg_neg] using hd)
      b (deriv b) hbc (fun t ht ↦ hb (hgap.trans ht.1.le))
    have hm₀ := hm (hgap.trans hc.1.le)
    have hcancel : Δ*m c = -Δ₁ := by
      apply mul_right_cancel₀ (hbpos (hgap.trans hc.1.le)).ne'
      rw [mul_assoc]
      change (b v-b s)*(m c*deriv b c) = -(deriv b v-deriv b s)*deriv b c
      linear_combination hcauchy
    exact ⟨hΔ₀, hΔmax, m c, hm₀.1, hm₀.2, by linarith only [hcancel]⟩
  obtain ⟨hΔ₀, hΔmax, μ, hμ, hμmax, hΔ₁⟩ := hsec
  obtain ⟨hH₀, _, hL, hLmax, hq₀, hq⟩ := profile_bounds_three hh hgap
  obtain ⟨_, _, hLv, hLvmax, _, _⟩ := profile_bounds_three hh hv₃
  obtain ⟨he, hemax, he₁⟩ := radical_error_bounds hh hhmax hgap
  change -(1/6 : ℝ) ≤ ε at he
  change ε ≤ 1/6 at hemax
  change -(1/5 : ℝ) ≤ ε₁ at he₁
  have hδL : profileSlope h v - L ≤ 1/18 := by
    rcases hsv.eq_or_lt with hEq | hlt
    · simp [L, hEq]
    obtain ⟨t, ht, hm⟩ := exists_hasDerivAt_eq_slope (profileSlope h)
      (profileCurvature h) hlt
      (fun t ht ↦ (hasDerivAt_profileSlope hh (hs.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht ↦ hasDerivAt_profileSlope hh (hs.trans ht.1))
    have heq := (eq_div_iff (sub_pos.mpr hlt).ne').mp hm
    have haEq : v-s = a := by dsimp [s]; ring
    rw [haEq] at heq
    change profileSlope h v - profileSlope h s ≤ _
    rw [← heq]
    exact (mul_le_mul (profile_bounds_three hh (hgap.trans ht.1.le)).2.2.2.2.2
      hamax ha (by norm_num)).trans_eq (by norm_num)
  have hζ : 1/3 ≤ ζ := by dsimp only [ζ]; linarith
  have hζmax : ζ ≤ 19/12 := by dsimp only [ζ]; linarith
  have hc₀ : ζ-4*L+2*ε ≤ -(49/36 : ℝ) := by dsimp only [ζ]; linarith
  have hc₁ : ε*(μ+m s-ζ)-ε₁ ≤ 13/15 := by
    obtain ⟨hms, hmsmax⟩ := hm hgap
    have ha₀ : 0 ≤ μ+m s-ζ := by linarith
    have ham : μ+m s-ζ ≤ 4 := by linarith
    linarith only [mul_le_mul hemax ham ha₀ (by norm_num : (0 : ℝ) ≤ 1/6), he₁]
  have hc₂ : (L^2+q)*(ζ/2-μ)+L*q+q₁/2 ≤ 0 := by
    have hm₁ := mul_le_mul_of_nonneg_left (show ζ/2-μ ≤ -(3/8 : ℝ) by linarith)
      (add_nonneg (sq_nonneg L) hq₀)
    have hm₂ : L*q ≤ q := mul_le_of_le_one_left hq₀ hLmax
    have hm₃ : (2/3 : ℝ)^2 ≤ L^2 := pow_le_pow_left₀ (by norm_num) hL 2
    have hq₁ : q₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq₀)
      (show 0 ≤ h+2*upperTailSlope h s by positivity)
    linarith only [hm₁, hm₂, hm₃, hq₁, hq]
  have hpoly : ζ*M + M₁ = (ζ-4*L+2*ε)*x^2 +
      Δ*x*(ε*(μ+m s-ζ)-ε₁) + Δ^2*((L^2+q)*(ζ/2-μ)+L*q+q₁/2) := by
    dsimp only [M, M₁]
    rw [hb₂, hb₃, hΔ₁]
    dsimp only [m, ε, L]
    ring
  let W := leftStripWeight h a v
  have hW : 0 < W := by unfold W leftStripWeight; positivity
  change _ ≤ -(167/180 : ℝ)*W*x^2 ∧ -(167/180 : ℝ)*W*x^2 < 0
  refine ⟨?_, mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hW) (sq_pos_of_pos hx)⟩
  rw [leftStrip_radical_mixed_formula_of_pos hh hv hs (hS hgap) (hS hv₃)]
  change W*(ζ*M+M₁) ≤ _
  rw [hpoly]
  have hmain := mul_le_mul_of_nonneg_right hc₀ (sq_nonneg x)
  have hlin := mul_le_mul_of_nonneg_left hc₁ (mul_nonneg hΔ₀ hx.le)
  have hlin' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hΔmax hx.le) (by norm_num : (0 : ℝ) ≤ 13/15)
  have hsq := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Δ) hc₂
  calc
    _ ≤ W * (-(167/180 : ℝ)*x^2) := mul_le_mul_of_nonneg_left
      (by nlinarith only [hmain, hlin, hlin', hsq]) hW.le
    _ = _ := by ring

#print axioms leftStrip_radical_correlated_le

end RefinedBMV.PositiveCenter
