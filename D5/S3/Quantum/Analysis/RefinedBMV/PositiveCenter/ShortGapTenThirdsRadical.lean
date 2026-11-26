/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirdsRadical
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds on the radical and the full numerator of its derivative. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapCorrection
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapTenThirdsAbsorption

open Set

namespace RefinedBMV.PositiveCenter

open private shortGap_exp_neg_four_le marginalLambda_antitone shortGap_root_lower
  shortGap_gap_le_rational from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapCorrection

open private radicalRateFactor hasDerivAt_radicalRateFactor from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical

/-- The full gap factor in the derivative of the marginal radical. -/
noncomputable def shortGapRadicalFactor (h t : ℝ) : ℝ :=
  (1 + h) * upperTailGap h t - 1 + Real.exp (-((1 + h) * t))

private theorem shortGapRadicalFactor_mono {h : ℝ} (hh : 0 < h) :
    MonotoneOn (shortGapRadicalFactor h) (Ici 0) := by
  have hd (t : ℝ) := hasDerivAt_radicalRateFactor (t := t) hh
  have hdiff : Differentiable ℝ (shortGapRadicalFactor h) := fun t =>
    (hd t).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    hdiff.continuous.continuousOn hdiff.differentiableOn
  intro t ht
  have ht₀ : 0 ≤ t := interior_subset ht
  have hd' : HasDerivAt (shortGapRadicalFactor h)
      ((1 + h) * (Real.exp (-(h * t)) - Real.exp (-((1 + h) * t)))) t := hd t
  rw [hd'.deriv]
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.exp_le_exp.mpr
    (by nlinarith only [ht₀])))

theorem shortGapRadicalFactor_nonneg {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    0 ≤ shortGapRadicalFactor h t := by
  have h := shortGapRadicalFactor_mono hh self_mem_Ici ht ht
  simpa [shortGapRadicalFactor, upperTailGap] using h

private theorem shortGapRadical_mu_le {h : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11) :
    Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) ≤
      (120 / 113) * (1 + (17 / 16) * h) := by
  have h1 : h ^ 2 ≤ (3 / 11) * h := by
    nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr hhmax)]
  have h2 : h ^ 3 ≤ (3 / 11) ^ 2 * h := by
    have h := mul_le_mul_of_nonneg_right h1 hh.le
    nlinarith only [h, mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3 / 11)]
  have hpoly : (3 + h) * (3 + 2 * h) * (1 + h) ≤ (3 * (1 + (17 / 16) * h)) ^ 2 := by
    nlinarith only [h1, h2, hh.le]
  have hs : (113 / 40 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
  calc
    _ ≤ Real.sqrt ((3 * (1 + (17 / 16) * h)) ^ 2 / 8) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hpoly (by norm_num))
    _ = (3 * (1 + (17 / 16) * h)) / Real.sqrt 8 := by
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ ≤ (3 * (1 + (17 / 16) * h)) / (113 / 40) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
    _ = _ := by ring

/-- A rational multiple bounds the full weighted radical derivative factor after four. -/
theorem shortGapRadical_weighted_factor_le {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) * shortGapRadicalFactor h t ≤
      (120 / 113) * (t - 1 + Real.exp (-t)) := by
  let a : ℝ := 17 / 16
  let f := 1 - Real.exp (-t)
  let b := 1 + h * t / 2
  let G := shortGapRadicalFactor h t
  have ht₀ : 0 ≤ t := by linarith
  have hb : 0 < b := by dsimp only [b]; positivity
  have hf : (51 / 52 : ℝ) ≤ f := by
    have he := (Real.exp_le_exp.mpr (neg_le_neg ht)).trans shortGap_exp_neg_four_le
    dsimp only [f]
    linarith only [he]
  have hG₀ : 0 ≤ G := shortGapRadicalFactor_nonneg hh ht₀
  have hG : G ≤ (1 + h) * (t / b) - f := by
    have he := Real.exp_le_exp.mpr (show -((1 + h) * t) ≤ -t by
      nlinarith only [mul_nonneg hh.le ht₀])
    have h := mul_le_mul_of_nonneg_left (shortGap_gap_le_rational hh ht₀)
      (show 0 ≤ 1 + h by positivity)
    dsimp only [G, shortGapRadicalFactor, b, f]
    linarith only [he, h]
  have ht' : 0 ≤ t - 4 := by linarith
  have htf : 0 ≤ 1 - f / 2 := by
    dsimp only [f]
    linarith only [(Real.exp_pos (-t)).le]
  have hH := mul_le_mul hhmax
    (show 1 - f / 2 ≤ (53 / 104 : ℝ) by linarith only [hf]) htf
    (by norm_num)
  have hH' := mul_le_mul_of_nonneg_left hH (show 0 ≤ a * t by
    dsimp only [a]; positivity)
  have hpoly : 0 ≤ t * (t / 2 - 1 - a - a * (3 / 11) * (53 / 104)) +
      a * (51 / 52) := by
    dsimp only [a]
    nlinarith only [ht', sq_nonneg (t - 4)]
  have hbudget : 0 ≤ t * (t / 2 - 1 - a) + a * f - a * h * t * (1 - f / 2) := by
    have hf' := mul_le_mul_of_nonneg_left hf (show 0 ≤ a by dsimp only [a]; norm_num)
    nlinarith only [hH', hpoly, hf']
  have hcompare : (1 + a * h) * ((1 + h) * (t / b) - f) ≤ t - f := by
    rw [← mul_le_mul_iff_left₀ hb]
    have he :
        (t - f) * b - (1 + a * h) * ((1 + h) * (t / b) - f) * b =
          h * (t * (t / 2 - 1 - a) + a * f - a * h * t * (1 - f / 2)) := by
      field_simp [hb.ne']
      dsimp only [b]
      ring
    apply sub_nonneg.mp
    rw [he]
    exact mul_nonneg hh.le hbudget
  calc
    _ ≤ ((120 / 113) * (1 + a * h)) * G :=
      mul_le_mul_of_nonneg_right (shortGapRadical_mu_le hh hhmax) hG₀
    _ ≤ ((120 / 113) * (1 + a * h)) * ((1 + h) * (t / b) - f) :=
      mul_le_mul_of_nonneg_left hG (by dsimp only [a]; positivity)
    _ = (120 / 113) * ((1 + a * h) * ((1 + h) * (t / b) - f)) := by ring
    _ ≤ (120 / 113) * (t - f) := mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ = _ := by dsimp only [f]; ring

theorem shortGapRadical_weighted_factor_le_four {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht₀ : 0 ≤ t) (ht₄ : t ≤ 4) :
    Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) * shortGapRadicalFactor h t ≤
      (120 / 113) * (157 / 52) := by
  have hmono := shortGapRadicalFactor_mono hh ht₀ (by norm_num : (4 : ℝ) ∈ Ici 0) ht₄
  calc
    _ ≤ Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) * shortGapRadicalFactor h 4 :=
      mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)
    _ ≤ (120 / 113) * (4 - 1 + Real.exp (-4)) :=
      shortGapRadical_weighted_factor_le hh hhmax le_rfl
    _ ≤ _ := by linarith only [shortGap_exp_neg_four_le]

private theorem shortGapRadical_lambda_upper {h t : ℝ} (hh : 0 < h) (ht : 1 ≤ t) :
    upperTailLambda h t ≤ (1 + 3 * t) * Real.exp (-(3 * t)) +
      (9 / 2) * t ^ 2 * Real.exp (-(2 * t)) := by
  let s := upperTailGap h t
  let g : ℝ := 3 + h
  let c := (3 + h) * (3 + 2 * h) / 2
  have ht₀ : 0 < t := by linarith
  have hs : 0 ≤ s := by
    rw [show s = t * expGapMean h t from expGapMean_eq hh t]
    exact mul_nonneg ht₀.le (expGapMean_pos _ _).le
  have hgp : 0 ≤ g := by dsimp only [g]; positivity
  have hs₁ : s ≤ t := upperTailGap_le hh
  have hA : 1 + g * t ≤ (1 + 3 * t) * Real.exp (h * t) := by
    have he := Real.add_one_le_exp (h * t)
    calc
      _ ≤ (1 + 3 * t) * (1 + h * t) := by
        dsimp only [g]
        nlinarith only [mul_nonneg hh.le (sq_nonneg t)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [he]) (by positivity)
  have hfirst : (1 + g * s) * Real.exp (-(g * t)) ≤
      (1 + 3 * t) * Real.exp (-(3 * t)) := calc
    _ ≤ (1 + g * t) * Real.exp (-(g * t)) :=
      mul_le_mul_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_left hs₁ hgp])
        (Real.exp_pos _).le
    _ ≤ ((1 + 3 * t) * Real.exp (h * t)) * Real.exp (-(g * t)) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [g]
      ring
  have hc : c ≤ (9 / 2) * (1 + h / 2) ^ 2 := by dsimp only [c]; nlinarith only [sq_nonneg h]
  have hss : s * (1 + h / 2) ≤ t := calc
    _ ≤ s * (1 + h * t / 2) := by
      apply mul_le_mul_of_nonneg_left _ hs
      nlinarith only [mul_le_mul_of_nonneg_left ht hh.le]
    _ ≤ _ := (le_div_iff₀ (by positivity)).mp (shortGap_gap_le_rational hh ht₀.le)
  have hsecond : c * s ^ 2 ≤ (9 / 2) * t ^ 2 := calc
    _ ≤ ((9 / 2) * (1 + h / 2) ^ 2) * s ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = (9 / 2) * (s * (1 + h / 2)) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hss 2) (by norm_num)
  exact add_le_add hfirst (mul_le_mul_of_nonneg_right hsecond (Real.exp_pos _).le)

private theorem radical_root_of_cutoff {h t T b : ℝ}
    (hh : 0 < h) (hT : 1 ≤ T) (ht : T ≤ t) (hb₀ : 0 ≤ b)
    (hcap : (1 + 3 * T) * Real.exp (-(3 * T)) + (9 / 2) * T ^ 2 * Real.exp (-(2 * T)) ≤
      1 - b ^ 2) : b ≤ Real.sqrt (1 - upperTailLambda h t) := by
  have hΛ := marginalLambda_antitone hh
    (show 0 ≤ T by linarith) (show 0 ≤ t by linarith) ht
  have h := (hΛ.trans (shortGapRadical_lambda_upper hh hT)).trans hcap
  exact Real.le_sqrt_of_sq_le (by linarith only [h])

theorem shortGapRadical_root_ten_thirds {h t : ℝ} (hh : 0 < h) (ht : 10 / 3 ≤ t) :
    (24 / 25 : ℝ) ≤ Real.sqrt (1 - upperTailLambda h t) := by
  apply radical_root_of_cutoff hh (by norm_num) ht (by norm_num)
  have he : Real.exp (-(10 / 3 : ℝ)) ≤ 1 / 28 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 3) 11
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h]
  have h2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
  have h3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
  rw [← Real.exp_nat_mul] at h2 h3
  norm_num at h2 h3 ⊢
  linarith only [h2, h3]

theorem shortGapRadical_root_four {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    (50 / 51 : ℝ) ≤ Real.sqrt (1 - upperTailLambda h t) :=
  shortGap_root_lower hh hhmax ht

theorem shortGapRadical_root_five {h t : ℝ} (hh : 0 < h) (ht : 5 ≤ t) :
    (997 / 1000 : ℝ) ≤ Real.sqrt (1 - upperTailLambda h t) := by
  apply radical_root_of_cutoff hh (by norm_num) ht (by norm_num)
  have he : Real.exp (-5 : ℝ) ≤ 1 / 148 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 13
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h]
  have h2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
  have h3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
  rw [← Real.exp_nat_mul] at h2 h3
  norm_num at h2 h3 ⊢
  linarith only [h2, h3]

/-- The exact radical derivative is absorbed by the two normalization factors from ten thirds. -/
theorem shortGap_correction_lt_from_ten_thirds {h u v jd αu αv : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 10 / 3 ≤ u) (huv : u < v)
    (hdmax : v - u ≤ 2)
    (hJ : jd ≤ Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) *
      Real.exp (3 * (v - u) / 2))
    (hJsharp : 1 ≤ v - u → jd ≤ (43 / 50) *
      Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8) * Real.exp (3 * (v - u) / 2))
    (hαu : αu ≤ 1 / (2 * u)) (hαv : αv ≤ 1 / (2 * v)) :
    let z := fun t ↦ Real.sqrt (1 - upperTailLambda h t)
    let c := (3 + h) * (3 + 2 * h) / 2
    let ξ := c * upperTailGap h v * Real.exp (-((u + v) / 2))
    deriv z v * jd < ξ * (1 / 2 - αu) * (1 / 2 - αv) := by
  intro z c ξ
  let d := v - u
  let ρ : ℝ := if d ≤ 1 then 1 else 43 / 50
  let a := upperTailGap h v
  let G := shortGapRadicalFactor h v
  let μ := Real.sqrt ((3 + h) * (3 + 2 * h) * (1 + h) / 8)
  have hv := hu.trans huv.le
  have hu₀ : 0 < u := by linarith
  have hv₀ : 0 < v := hu₀.trans huv
  have ha : 0 < a := by
    rw [show a = v * expGapMean h v from expGapMean_eq hh v]
    exact mul_pos hv₀ (expGapMean_pos _ _)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hξ : 0 < ξ := mul_pos (mul_pos hc ha) (Real.exp_pos _)
  have hz₁ : (24 / 25 : ℝ) ≤ z v := shortGapRadical_root_ten_thirds hh hv
  have hz : 0 < z v := (by norm_num : (0 : ℝ) < 24 / 25).trans_le hz₁
  have hG₀ : 0 ≤ G := shortGapRadicalFactor_nonneg hh hv₀.le
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hJρ : jd ≤ ρ * μ * Real.exp (3 * d / 2) := by
    by_cases hd : d ≤ 1
    · simpa only [ρ, if_pos hd, one_mul] using hJ
    · simpa only [ρ, if_neg hd] using hJsharp (le_of_lt (lt_of_not_ge hd))
  have hzd : deriv z v = c * a * Real.exp (-(2 * v)) * G / z v := by
    have hΛ := hasDerivAt_upperTailLambda (t := v) hh
    have hroot : 0 < 1 - upperTailLambda h v := Real.sqrt_pos.mp hz
    have h := ((hasDerivAt_const v (1 : ℝ)).fun_sub hΛ).sqrt hroot.ne'
    change HasDerivAt z _ v at h
    rw [h.deriv]
    dsimp only [G, shortGapRadicalFactor, c, a, z]
    ring
  have hz' : 0 ≤ deriv z v := by
    rw [hzd]
    exact div_nonneg (by positivity) hz.le
  have hscore := shortGapTenThirds_absorption_scalar hu huv hdmax
    (mul_nonneg hμ hG₀)
    (shortGapRadical_weighted_factor_le_four hh hhmax hv₀.le)
    (shortGapRadical_weighted_factor_le hh hhmax) hz₁
    (shortGapRadical_root_four hh hhmax) (shortGapRadical_root_five hh)
  change ρ * (μ * G) * Real.exp (-u) <
    z v * ((1 - 1 / u) * (1 - 1 / v) / 4) at hscore
  have hdecay : Real.exp (-(2 * v)) * Real.exp (3 * d / 2) =
      Real.exp (-((u + v) / 2)) * Real.exp (-u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  have hscaled : deriv z v * (ρ * μ * Real.exp (3 * d / 2)) =
      ξ * (ρ * (μ * G) * Real.exp (-u) / z v) := by
    rw [hzd, show c * a * Real.exp (-(2 * v)) * G / z v *
      (ρ * μ * Real.exp (3 * d / 2)) =
      (c * a) * (Real.exp (-(2 * v)) * Real.exp (3 * d / 2)) *
        (ρ * (μ * G) / z v) by ring, hdecay]
    dsimp only [ξ, a]
    ring
  have hhalfU : 1 / (2 * u) = (1 / u) / 2 := by ring
  have hhalfV : 1 / (2 * v) = (1 / v) / 2 := by ring
  have hinvu : 1 / u ≤ (1 : ℝ) := (div_le_iff₀ hu₀).mpr (by linarith)
  have hinvv : 1 / v ≤ (1 : ℝ) := (div_le_iff₀ hv₀).mpr (by linarith)
  have hlast : (1 - 1 / u) * (1 - 1 / v) / 4 ≤ (1 / 2 - αu) * (1 / 2 - αv) := by
    rw [show (1 - 1 / u) * (1 - 1 / v) / 4 =
      ((1 - 1 / u) / 2) * ((1 - 1 / v) / 2) by ring]
    rw [hhalfU] at hαu
    rw [hhalfV] at hαv
    exact mul_le_mul (by linarith only [hαu]) (by linarith only [hαv])
      (by linarith only [hinvv]) (by linarith only [hαu, hinvu])
  calc
    _ ≤ deriv z v * (ρ * μ * Real.exp (3 * d / 2)) :=
      mul_le_mul_of_nonneg_left hJρ hz'
    _ = ξ * (ρ * (μ * G) * Real.exp (-u) / z v) := hscaled
    _ < ξ * ((1 - 1 / u) * (1 - 1 / v) / 4) :=
      mul_lt_mul_of_pos_left ((div_lt_iff₀ hz).mpr (by simpa only [mul_comm] using hscore)) hξ
    _ ≤ ξ * ((1 / 2 - αu) * (1 / 2 - αv)) := mul_le_mul_of_nonneg_left hlast hξ.le
    _ = _ := by ring

end RefinedBMV.PositiveCenter
