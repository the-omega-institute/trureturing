/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapCorrection
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds for the marginal derivative and short-gap correction. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailAverage
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CollisionRadicand

/-! # The marginal derivative and the short-gap correction -/

open Set

namespace RefinedBMV.PositiveCenter

private theorem shortGap_exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 52 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
  linarith only [h]

private theorem marginalLambda_antitone {h : ℝ} (hh : 0 < h) :
    AntitoneOn (upperTailLambda h) (Ici 0) := by
  have hdiff : Differentiable ℝ (upperTailLambda h) := fun t ↦
    (hasDerivAt_upperTailLambda (t := t) hh).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hdiff.continuous.continuousOn
    hdiff.differentiableOn
  intro t ht
  exact neg_nonneg.mp (upperTailLambda_deriv_bounds hh (interior_subset ht)).1

private theorem shortGap_root_lower {h v : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hv : 4 ≤ v) : (50 / 51 : ℝ) ≤ Real.sqrt (1 - upperTailLambda h v) := by
  let g : ℝ := 3 + h
  let k : ℝ := 3 + 2*h
  let c : ℝ := g*k/2
  let a := upperTailGap h 4
  have hΛ := marginalLambda_antitone hh (by norm_num : (4 : ℝ) ∈ Ici 0)
    (show v ∈ Ici 0 from le_trans (by norm_num) hv) hv
  have ha : 0 ≤ a := by
    have he : Real.exp (-(h*4)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_zero] at he
    exact div_nonneg (sub_nonneg.mpr he) hh.le
  have ha₄ : a ≤ 4 := upperTailGap_le hh
  have hga : g*a ≤ 16 := by
    have hg₄ : g ≤ 4 := by dsimp [g]; linarith
    calc
      _ ≤ 4*4 := mul_le_mul hg₄ ha₄ ha (by norm_num)
      _ = _ := by norm_num
  have hc : c ≤ 6 := by
    dsimp [c, g, k]
    nlinarith only [hhmax, mul_le_mul_of_nonneg_left hhmax hh.le]
  have hca : c*a^2 ≤ 96 := calc
    _ ≤ 6*4^2 := mul_le_mul hc (pow_le_pow_left₀ ha ha₄ 2) (sq_nonneg a) (by norm_num)
    _ = _ := by norm_num
  have he₁₂ : Real.exp (-(g*4)) ≤ (1/52)^3 := calc
    _ ≤ Real.exp (-12) := Real.exp_le_exp.mpr (by dsimp [g]; linarith)
    _ = Real.exp (-4)^3 := by
      simpa only [Nat.cast_ofNat, show (3 : ℝ)*(-4) = -12 by norm_num] using
        Real.exp_nat_mul (-4 : ℝ) 3
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le shortGap_exp_neg_four_le 3
  have he₈ : Real.exp (-(2*4 : ℝ)) ≤ (1/52)^2 := calc
    _ = Real.exp (-4)^2 := by
      convert Real.exp_nat_mul (-4 : ℝ) 2 using 2
      norm_num
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le shortGap_exp_neg_four_le 2
  have hA : (1+g*a)*Real.exp (-(g*4)) ≤ 17*(1/52)^3 :=
    mul_le_mul (by linarith only [hga]) he₁₂ (Real.exp_pos _).le (by norm_num)
  have hB : c*a^2*Real.exp (-(2*4 : ℝ)) ≤ 96*(1/52)^2 :=
    mul_le_mul hca he₈ (Real.exp_pos _).le (by norm_num)
  change upperTailLambda h v ≤ (1+g*a)*Real.exp (-(g*4)) +
    c*a^2*Real.exp (-(2*4 : ℝ)) at hΛ
  have hcap : (17*(1/52)^3 + 96*(1/52)^2 : ℝ) ≤ 1-(50/51)^2 := by norm_num
  have hΛbound := (hΛ.trans (add_le_add hA hB)).trans hcap
  apply Real.le_sqrt_of_sq_le
  norm_num at hΛbound ⊢
  linarith only [hΛbound]

private theorem marginal_deriv_bounds_of_root {h v : ℝ} (hh : 0 < h) (hv : 0 < v)
    (hz₀ : 0 < Real.sqrt (1 - upperTailLambda h v)) :
    let z := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
    let c := (3+h)*(3+2*h)/2
    let B := c*(upperTailGap h v)^2*Real.exp (-(2*v))
    0 ≤ deriv z v ∧ deriv z v ≤ B / z v := by
  let z : ℝ → ℝ := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
  let c : ℝ := (3+h)*(3+2*h)/2
  let a := upperTailGap h v
  let b := Real.exp (-(h*v))
  let B := c*a^2*Real.exp (-(2*v))
  change 0 ≤ deriv z v ∧ deriv z v ≤ B / z v
  have hb : 0 < b := Real.exp_pos _
  have hrel : h*a = 1-b := by
    dsimp [a, b, upperTailGap]
    field_simp [hh.ne']
  have ha : 0 ≤ a := by
    have hlt : b < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv))
    exact div_nonneg (sub_nonneg.mpr hlt.le) hh.le
  have hB : 0 ≤ B := by dsimp only [B, c]; positivity
  have hr : 0 < 1 - upperTailLambda h v := Real.sqrt_pos.mp hz₀
  have hd : HasDerivAt (upperTailLambda h) (deriv (upperTailLambda h) v) v :=
    (hasDerivAt_upperTailLambda hh).differentiableAt.hasDerivAt
  have hdz : HasDerivAt z (-deriv (upperTailLambda h) v / (2*z v)) v := by
    simpa only [zero_sub, z] using
      ((hasDerivAt_const v (1 : ℝ)).fun_sub hd).sqrt hr.ne'
  have hsign := (upperTailLambda_deriv_bounds hh hv.le).1
  have he : Real.exp (-((1+h)*v)) = b*Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbracket : (1+h)*a - 1 + Real.exp (-((1+h)*v)) ≤ a := by
    rw [he]
    have he₀ : Real.exp (-v) ≤ 1 := (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)).le
    have hbe : b*Real.exp (-v) ≤ b := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he₀ hb.le
    nlinarith only [hrel, hbe]
  have hupper : -deriv (upperTailLambda h) v ≤ 2*B := calc
    _ = (2*c*Real.exp (-(2*v))*a)*((1+h)*a - 1 + Real.exp (-((1+h)*v))) := by
      rw [(hasDerivAt_upperTailLambda (t := v) hh).deriv]
      dsimp only [c, a]
      ring
    _ ≤ (2*c*Real.exp (-(2*v))*a)*a :=
      mul_le_mul_of_nonneg_left hbracket (by dsimp only [c]; positivity)
    _ = _ := by dsimp only [B]; ring
  have hden : 0 < 2*z v := by positivity
  rw [hdz.deriv]
  refine ⟨div_nonneg hsign hden.le, ?_⟩
  calc
    _ ≤ (2*B)/(2*z v) := div_le_div_of_nonneg_right hupper hden.le
    _ = B / z v := by ring

/-- The marginal slope is bounded by the second summand divided by the root. -/
theorem shortGap_marginal_deriv_bounds {h v : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hv : 4 ≤ v) :
    let z := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
    let c := (3+h)*(3+2*h)/2
    let B := c*(upperTailGap h v)^2*Real.exp (-(2*v))
    0 ≤ deriv z v ∧ deriv z v ≤ (51/50)*B := by
  let z : ℝ → ℝ := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
  let B := ((3+h)*(3+2*h)/2)*(upperTailGap h v)^2*Real.exp (-(2*v))
  have hz := shortGap_root_lower hh hhmax hv
  have hz₀ : 0 < z v := (by norm_num : (0 : ℝ) < 50/51).trans_le hz
  obtain ⟨h₀, h₁⟩ := marginal_deriv_bounds_of_root hh (by linarith) hz₀
  refine ⟨h₀, h₁.trans ?_⟩
  change B / z v ≤ (51/50)*B
  apply (div_le_iff₀ hz₀).mpr
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    B = ((51/50)*B)*(50/51) := by ring
    _ ≤ ((51/50)*B)*z v := mul_le_mul_of_nonneg_left hz (by positivity)

/-- The marginal root and its slope on gaps at least two. -/
theorem middleGap_marginal_bounds {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 2 ≤ t) :
    let z := fun v ↦ Real.sqrt (1 - upperTailLambda h v)
    0 ≤ z t ∧ z t ≤ 1 ∧ 0 ≤ deriv z t ∧ deriv z t ≤ 7 / 10 := by
  let z : ℝ → ℝ := fun v ↦ Real.sqrt (1 - upperTailLambda h v)
  let c : ℝ := (3 + h) * (3 + 2*h) / 2
  let a := upperTailGap h
  have ht₀ : 0 < t := by linarith
  have ha (v : ℝ) (hv : 0 ≤ v) : 0 ≤ a v := by
    unfold a upperTailGap
    exact div_nonneg (sub_nonneg.mpr ((Real.exp_le_one_iff).mpr
      (neg_nonpos.mpr (mul_nonneg hh.le hv)))) hh.le
  have hc : c ≤ 6 := by
    dsimp [c]
    nlinarith only [hhmax, mul_le_mul_of_nonneg_left hhmax hh.le]
  have he4 : Real.exp (-4 : ℝ) ≤ 1 / 54 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h]
  have he6 : Real.exp (-6 : ℝ) ≤ 1 / 380 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h]
  have hΛ := marginalLambda_antitone hh (by norm_num : (2 : ℝ) ∈ Ici 0)
    (show t ∈ Ici 0 from ht₀.le) ht
  have hA : (1 + (3 + h) * a 2) * Real.exp (-((3 + h) * 2)) ≤ 9 / 380 := by
    have hg : (3 + h) * a 2 ≤ (4 : ℝ) * 2 :=
      mul_le_mul (by linarith) (upperTailGap_le hh) (ha 2 (by norm_num)) (by norm_num)
    have he := (Real.exp_le_exp.mpr (show -((3 + h) * 2) ≤ -6 by linarith)).trans he6
    calc
      _ ≤ 9 * (1 / 380) := mul_le_mul (by linarith) he (Real.exp_pos _).le (by norm_num)
      _ = _ := by ring
  have hB₂ : c * a 2 ^ 2 * Real.exp (-(2 * 2 : ℝ)) ≤ 24 / 54 := by
    have ha₂ : a 2 ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (ha 2 (by norm_num)) (upperTailGap_le hh) 2
    have hb := mul_le_mul hc ha₂ (sq_nonneg _) (by norm_num)
    have he : Real.exp (-(2 * 2 : ℝ)) ≤ 1 / 54 := by convert he4 using 2 <;> norm_num
    nlinarith only [mul_le_mul hb he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 6 * 2 ^ 2)]
  change upperTailLambda h t ≤ (1 + (3 + h) * a 2) * Real.exp (-((3 + h) * 2)) +
    c * a 2 ^ 2 * Real.exp (-(2 * 2 : ℝ)) at hΛ
  have hz : (7 / 10 : ℝ) ≤ z t := Real.le_sqrt_of_sq_le (by
    have hcap := hΛ.trans (add_le_add hA hB₂)
    norm_num at hcap ⊢
    linarith only [hcap])
  have hz₀ : 0 < z t := (by norm_num : (0 : ℝ) < 7/10).trans_le hz
  have hz₁ : z t ≤ 1 := by
    have hΛ₀ : 0 ≤ upperTailLambda h t := by
      unfold upperTailLambda
      change 0 ≤ (1 + (3 + h) * a t) * _ + c * (a t)^2 * _
      have ha₀ := ha t ht₀.le
      have hc₀ : 0 ≤ c := by dsimp [c]; positivity
      positivity
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (sub_le_self 1 hΛ₀)
  have hdecay : a t * Real.exp (-t) ≤ 2 * Real.exp (-2) := calc
    _ ≤ t * Real.exp (-t) := mul_le_mul_of_nonneg_right (upperTailGap_le hh) (Real.exp_pos _).le
    _ ≤ (2 * Real.exp (t - 2)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (t - 2)]) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, show t - 2 + -t = -2 by ring]
  have hdecaySq : a t ^ 2 * Real.exp (-(2 * t)) ≤ 4 / 54 := calc
    _ = (a t * Real.exp (-t)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> push_cast <;> ring
    _ ≤ (2 * Real.exp (-2)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (ha t ht₀.le) (Real.exp_pos _).le) hdecay 2
    _ = 4 * Real.exp (-4) := by rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    _ ≤ _ := by linarith only [he4]
  have hB : c * a t ^ 2 * Real.exp (-(2 * t)) ≤ 24 / 54 := calc
    _ = c * (a t ^ 2 * Real.exp (-(2 * t))) := by ring
    _ ≤ 6 * (4 / 54) := mul_le_mul hc hdecaySq (by positivity) (by norm_num)
    _ = _ := by ring
  obtain ⟨hderiv₀, hderiv₁⟩ := marginal_deriv_bounds_of_root hh ht₀ hz₀
  refine ⟨hz₀.le, hz₁, hderiv₀, hderiv₁.trans ?_⟩
  change c * a t ^ 2 * Real.exp (-(2 * t)) / z t ≤ 7 / 10
  apply (div_le_iff₀ hz₀).mpr
  linarith only [hB, hz]

private theorem shortGap_gap_le_rational {h v : ℝ} (hh : 0 < h) (hv : 0 ≤ v) :
    upperTailGap h v ≤ v/(1+h*v/2) := by
  let f : ℝ → ℝ := fun x ↦ (1+x/2)*Real.exp (-x) - (1-x/2)
  have hderiv (x : ℝ) :
      HasDerivAt f ((1-(1+x)*Real.exp (-x))/2) x := by
    have hline := ((hasDerivAt_id' x).div_const 2).const_add 1
    have hline' := HasDerivAt.const_sub 1 ((hasDerivAt_id' x).div_const 2)
    have hexp : HasDerivAt (fun y ↦ Real.exp (-y)) (Real.exp (-x)*(-1)) x :=
      (HasDerivAt.neg (hasDerivAt_id' x)).exp
    apply ((hline.mul hexp).sub hline').congr_deriv
    ring
  have hdiff : Differentiable ℝ f := fun x ↦ (hderiv x).differentiableAt
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro x _
    rw [(hderiv x).deriv]
    have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
    linarith only [hm]
  have h0 : f 0 = 0 := by simp [f]
  have hf := hmono self_mem_Ici (show h*v ∈ Ici 0 from mul_nonneg hh.le hv)
    (mul_nonneg hh.le hv)
  rw [h0] at hf
  dsimp only [f] at hf
  have hden : 0 < 1+h*v/2 := by positivity
  apply (le_div_iff₀ hden).mpr
  rw [upperTailGap, div_mul_eq_mul_div]
  apply (div_le_iff₀ hh).mpr
  nlinarith only [hf]

private theorem shortGap_weighted_gap_le {h v : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hv : 4 ≤ v) :
    upperTailGap h v * Real.sqrt ((3+h)*(3+2*h)*(1+h)/8) ≤ 3*v/Real.sqrt 8 := by
  have hv₀ : 0 < v := by linarith
  have he := (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv₀))).le
  have ha : 0 ≤ upperTailGap h v := div_nonneg (sub_nonneg.mpr he) hh.le
  have hp : (3+h)*(3+2*h)*(1+h) ≤ (3*(1+2*h))^2 := by
    have hh₁ : 0 ≤ 1-h := by linarith
    nlinarith only [mul_nonneg (sq_nonneg h) hh₁, hh.le, sq_nonneg h]
  have hs : Real.sqrt ((3+h)*(3+2*h)*(1+h)/8) ≤ 3*(1+2*h)/Real.sqrt 8 := by
    calc
      _ ≤ Real.sqrt ((3*(1+2*h))^2/8) := Real.sqrt_le_sqrt (by linarith only [hp])
      _ = _ := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have ha' := (le_div_iff₀ (by positivity : 0 < 1+h*v/2)).mp
    (shortGap_gap_le_rational hh hv₀.le)
  have hav : upperTailGap h v * (1+2*h) ≤ v := calc
    _ ≤ upperTailGap h v * (1+h*v/2) := by
      apply mul_le_mul_of_nonneg_left _ ha
      nlinarith only [mul_le_mul_of_nonneg_left hv hh.le]
    _ ≤ _ := ha'
  calc
    _ ≤ upperTailGap h v*(3*(1+2*h)/Real.sqrt 8) := mul_le_mul_of_nonneg_left hs ha
    _ = 3*(upperTailGap h v*(1+2*h))/Real.sqrt 8 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hav (by norm_num))
      (Real.sqrt_nonneg _)

private theorem shortGap_decay_budget {u d : ℝ} (hu : 4 ≤ u) (hd : d ≤ 2) :
    (u+d)*Real.exp (-u) ≤ 6*Real.exp (-4) := calc
  _ ≤ (6*Real.exp (u-4))*Real.exp (-u) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith only [hu, hd, Real.add_one_le_exp (u-4)]
  _ = _ := by
    rw [mul_assoc, ← Real.exp_add, show u-4 + -u = -4 by ring]

/-- The short-gap marginal correction is strictly below the contribution
from the two normalization slopes, given the upper bound on `J'`. -/
theorem shortGap_correction_lt {h u d jd αu αv : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 4 ≤ u) (hd : 0 < d) (hdmax : d ≤ 2)
    (hJ : jd ≤ Real.sqrt ((3+h)*(3+2*h)*(1+h)/8)*Real.exp (3*d/2))
    (hαu : αu ≤ 1/7) (hαv : αv ≤ 1/7) :
    let v := u+d
    let z := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
    let c := (3+h)*(3+2*h)/2
    let Ξ := c*upperTailGap h v*Real.exp (-(u+v)/2)
    deriv z v * jd < Ξ*(1/2-αu)*(1/2-αv) := by
  let v := u+d
  let a := upperTailGap h v
  let z : ℝ → ℝ := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
  let c : ℝ := (3+h)*(3+2*h)/2
  let Ξ := c*a*Real.exp (-(u+v)/2)
  let M := Real.sqrt ((3+h)*(3+2*h)*(1+h)/8)
  change deriv z v * jd < Ξ*(1/2-αu)*(1/2-αv)
  have hv : 4 ≤ v := by dsimp [v]; linarith
  have hv₀ : 0 < v := by linarith
  have ha : 0 < a :=
    div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv₀)))) hh
  have hΞ : 0 < Ξ := by dsimp only [Ξ, c]; positivity
  have hz := shortGap_marginal_deriv_bounds hh hhmax hv
  change 0 ≤ deriv z v ∧ deriv z v ≤ (51/50)*(c*a^2*Real.exp (-(2*v))) at hz
  have hscale : a*M ≤ 3*v/Real.sqrt 8 := shortGap_weighted_gap_le hh hhmax hv
  have hdecay : v*Real.exp (-u) ≤ 6*Real.exp (-4) := shortGap_decay_budget hu hdmax
  have hexp : Real.exp (-(2*v))*Real.exp (3*d/2) =
      Real.exp (-(u+v)/2)*Real.exp (-u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [v]
    ring
  have hbound : deriv z v * jd ≤ Ξ*((51/50)*(18/Real.sqrt 8)*Real.exp (-4)) := calc
    _ ≤ deriv z v*(M*Real.exp (3*d/2)) := mul_le_mul_of_nonneg_left hJ hz.1
    _ ≤ ((51/50)*(c*a^2*Real.exp (-(2*v))))*(M*Real.exp (3*d/2)) :=
      mul_le_mul_of_nonneg_right hz.2 (by dsimp only [M]; positivity)
    _ = ((51/50)*Ξ*Real.exp (-u))*(a*M) := by
      rw [show (51/50)*(c*a^2*Real.exp (-(2*v)))*(M*Real.exp (3*d/2)) =
        (51/50)*(c*a)*(a*M)*(Real.exp (-(2*v))*Real.exp (3*d/2)) by ring, hexp]
      dsimp only [Ξ]
      ring
    _ ≤ ((51/50)*Ξ*Real.exp (-u))*(3*v/Real.sqrt 8) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (Ξ*((51/50)*(3/Real.sqrt 8)))*(v*Real.exp (-u)) := by ring
    _ ≤ (Ξ*((51/50)*(3/Real.sqrt 8)))*(6*Real.exp (-4)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring
  have hs : (14/5 : ℝ) < Real.sqrt 8 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hcoeff : (18 : ℝ)/Real.sqrt 8 ≤ 18/(14/5) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs.le
  have hnum : (51/50)*(18/Real.sqrt 8)*Real.exp (-4) < (1/2-1/7 : ℝ)^2 := calc
    (51/50)*(18/Real.sqrt 8)*Real.exp (-4) ≤ ((51/50)*(18/(14/5))*(1/52) : ℝ) := by
      apply mul_le_mul _ shortGap_exp_neg_four_le (Real.exp_pos _).le (by norm_num)
      exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
    _ < _ := by norm_num
  have hα : (1/2-1/7 : ℝ)^2 ≤ (1/2-αu)*(1/2-αv) := by
    rw [pow_two]
    exact mul_le_mul (by linarith only [hαu]) (by linarith only [hαv])
      (by norm_num) (by linarith only [hαu])
  calc
    _ ≤ Ξ*((51/50)*(18/Real.sqrt 8)*Real.exp (-4)) := hbound
    _ < Ξ*((1/2-1/7)^2) := mul_lt_mul_of_pos_left hnum hΞ
    _ ≤ Ξ*((1/2-αu)*(1/2-αv)) := mul_le_mul_of_nonneg_left hα hΞ.le
    _ = _ := by ring

/-- At gaps at least two the growth estimate for the square-root slope
controls the marginal correction without an upper cutoff on the gap. -/
theorem middleGap_correction_lt {h u d jd αu αv : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 4 ≤ u) (hd : 2 ≤ d)
    (hJ : jd ≤ (11 / 5) * Real.exp (3*d/2) / upperTailGap h d)
    (hαu : αu ≤ 1/7) (hαv : αv ≤ 1/7) :
    let v := u+d
    let z := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
    let c := (3+h)*(3+2*h)/2
    let Ξ := c*upperTailGap h v*Real.exp (-(u+v)/2)
    deriv z v * jd < Ξ*(1/2-αu)*(1/2-αv) := by
  let v := u+d
  let a := upperTailGap h
  let z : ℝ → ℝ := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
  let c := (3+h)*(3+2*h)/2
  let Ξ := c*a v*Real.exp (-(u+v)/2)
  have hv : 4 ≤ v := by dsimp [v]; linarith
  have ha {t : ℝ} (ht : 0 < t) : 0 < a t := by
    rw [show a t = t * expGapMean h t from expGapMean_eq hh t]
    exact mul_pos ht (expGapMean_pos _ _)
  have had : 0 < a d := ha (by linarith)
  have hav : 0 < a v := ha (by linarith)
  have hΞ : 0 < Ξ := by dsimp only [Ξ, c]; positivity
  obtain ⟨hz₀, hz₁⟩ := shortGap_marginal_deriv_bounds hh hhmax hv
  have hr : a v / a d ≤ 1 + u / 2 := calc
    _ ≤ v / d := by
      apply (div_le_div_iff₀ had (show 0 < d by linarith)).mpr
      dsimp only [a]
      rw [expGapMean_eq hh v, expGapMean_eq hh d]
      have hm := expGapMean_antitone hh.le (show h ≤ h from le_rfl)
        (show 0 ≤ d by linarith) (show d ≤ v by dsimp [v]; linarith)
      calc
        _ = (v*d)*expGapMean h v := by ring
        _ ≤ (v*d)*expGapMean h d := mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := by ring
    _ = 1 + u / d := by
      dsimp [v]
      field_simp
      ring
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (by linarith) (by norm_num) hd) 1
  have hdecay : (a v / a d) * Real.exp (-u) ≤ 3 * Real.exp (-4) := calc
    _ ≤ (1 + u / 2) * Real.exp (-u) := mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ ≤ (3 * Real.exp (u - 4)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (u - 4)]) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, show u - 4 + -u = -4 by ring]
  have hE : Real.exp (-(2*v))*Real.exp (3*d/2) =
      Real.exp (-(u+v)/2)*Real.exp (-u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [v]
    ring
  change deriv z v * jd < Ξ*(1/2-αu)*(1/2-αv)
  have hcap : deriv z v * jd ≤ Ξ*((51/50)*(11/5)*3*Real.exp (-4)) := calc
    _ ≤ deriv z v * ((11/5)*Real.exp (3*d/2)/a d) := mul_le_mul_of_nonneg_left hJ hz₀
    _ ≤ ((51/50)*(c*(a v)^2*Real.exp (-(2*v)))) * ((11/5)*Real.exp (3*d/2)/a d) :=
      mul_le_mul_of_nonneg_right hz₁ (by positivity)
    _ = (Ξ*((51/50)*(11/5))) * ((a v / a d) * Real.exp (-u)) := by
      calc
        _ = ((51/50)*(11/5)*c*(a v)^2/a d) *
            (Real.exp (-(2*v))*Real.exp (3*d/2)) := by ring
        _ = _ := by rw [hE]; dsimp [Ξ]; ring
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hdecay
        (show 0 ≤ Ξ*((51/50)*(11/5)) by positivity)
      calc
        _ ≤ (Ξ*((51/50)*(11/5)))*(3*Real.exp (-4)) := hmul
        _ = _ := by ring
  have he4 : Real.exp (-4 : ℝ) ≤ 1 / 54 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h]
  have hnum : (51/50)*(11/5)*3*Real.exp (-4) < (1/2-1/7 : ℝ)^2 := by
    linarith only [he4]
  have haα : (1/2-1/7 : ℝ)^2 ≤ (1/2-αu)*(1/2-αv) := by
    rw [pow_two]
    exact mul_le_mul (by linarith only [hαu]) (by linarith only [hαv])
      (by norm_num) (by linarith only [hαu])
  rw [mul_assoc]
  exact hcap.trans_lt ((mul_lt_mul_of_pos_left hnum hΞ).trans_le
    (mul_le_mul_of_nonneg_left haα hΞ.le))

end RefinedBMV.PositiveCenter
