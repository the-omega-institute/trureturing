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

private theorem abs_add_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x+y| ≤ X+Y := (abs_add_le x y).trans (add_le_add hx hy)

private theorem abs_sub_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x-y| ≤ X+Y := (abs_sub x y).trans (add_le_add hx hy)

private theorem abs_mul_bound {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x*y| ≤ X*Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

private theorem abs_sq_bound {x X : ℝ} (hx : |x| ≤ X) : |x^2| ≤ X^2 := by
  simpa only [pow_two] using abs_mul_bound hx hx

private theorem abs_half_bound {x X : ℝ} (hx : |x| ≤ X) : |x/2| ≤ X/2 := by
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right hx (by norm_num)

private theorem slope_bounds {h t : ℝ} (hh : 0 < h) (ht : 6 ≤ t) :
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
  obtain ⟨hL₀, hLmax, hLlo, hLhi, hq₀, hqhi⟩ := slope_bounds hh hgap
  obtain ⟨_, _, hVlo, hVhi, _, _⟩ := slope_bounds hh (hgap.trans hsv)
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

end RefinedBMV.PositiveCenter
