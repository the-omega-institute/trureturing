/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict negativity of the mixed derivative of the original kernel on the central strip at gap four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourMain
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourRadicalSign

/-! # The mixed derivative of the original kernel at gap four -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private tailLowerSlope tailBaseJet tailBaseJet_isAt tailLinear_smooth tailQuadratic_smooth
  tailCorrection_smooth tailCorrection_jet separatedMainJet from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet

private theorem separatedFour_mainJet_signs {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₄ : u ≤ 4) (hgap : 4 ≤ v - u) :
    0 < (separatedMainJet p u v).du ∧ (separatedMainJet p u v).duv < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let L := upperTailSlope h d
  let Lv := upperTailSlope h v
  let q := L * (h + L)
  let L₂ := deriv (deriv (upperTailSlope h)) d
  let b := tailLowerSlope p u
  let w := -1 / 2 + L - Lv / 2
  let f := upperTailRatio h u
  let f₁ := deriv (upperTailRatio h) u
  let r := 1 - L * f
  let s := -L * f₁
  let t := q * f
  let c : ℝ := (3 + h) * (3 + 2 * h) / 2
  let e₀ := upperTailLinearP0 h u * upperTailLinearW h 2 d / c
  let e₁ := upperTailLinearP1 h u * upperTailLinearW h 1 d / c
  let l₀ := deriv (upperTailLinearP0 h) u / upperTailLinearP0 h u
  let l₁ := deriv (upperTailLinearP1 h) u / upperTailLinearP1 h u
  let M₁ := 1 + h + L
  let M₂ := 1 + h + 2 * L
  let lower₀ := b - L + l₀ + M₂
  let lower₁ := b - L + l₁ + M₁
  let B := upperTailBaseFactor p u d
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := by dsimp only [h]; positivity
  have hu : 0 < u := by linarith only [hu₀]
  have hd₀ : 0 < d := (by norm_num : (0 : ℝ) < 4).trans_le hgap
  have huv : u < v := sub_pos.mp hd₀
  have hL₁ : deriv (upperTailSlope h) d = -q :=
    (hasDerivAt_upperTailSlope hh hd₀).deriv
  have hB : 0 < B := by
    have hC := compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hu.ne')
    have hβ (x : ℝ) (hx : 0 < x) : 0 < 1 - Real.exp (-(h * x)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hx)))
    have hN : 0 < ((p + 2).choose 2 : ℝ) := by
      exact_mod_cast (Nat.choose_pos (show 2 ≤ p + 2 by omega))
    dsimp only [B, upperTailBaseFactor]
    have hd' := hβ d hd₀
    have hv' := hβ (d + u) (by linarith)
    have hu' := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
    positivity
  have hR := tailCorrection_jet hh hu huv
  change upperGapJet (fun x y ↦ 1 - upperTailSlope h y * upperTailRatio h x) u v =
    (⟨r, -L * f₁ + deriv (upperTailSlope h) d * f,
      -deriv (upperTailSlope h) d * f, -deriv (upperTailSlope h) d * f₁ + L₂ * f⟩ :
      MixedJet ℝ) at hR
  rw [hL₁] at hR
  obtain ⟨he, heu, hed, heud, hedd⟩ := upperTailLinearError_derivatives hh hu hd₀
  change upperTailLinearError h u d = -e₀ + e₁ at he
  change deriv (fun x ↦ upperTailLinearError h x d) u = -l₀ * e₀ + l₁ * e₁ at heu
  change deriv (upperTailLinearError h u) d = M₂ * e₀ - M₁ * e₁ at hed
  change deriv (fun x ↦ deriv (upperTailLinearError h x) d) u =
    M₂ * l₀ * e₀ - M₁ * l₁ * e₁ at heud
  change deriv (deriv (upperTailLinearError h u)) d =
    -(M₂ ^ 2 + 2 * q) * e₀ + (M₁ ^ 2 + q) * e₁ at hedd
  have hE : upperGapJet (upperTailLinearError h) u v =
      (⟨-e₀ + e₁, -l₀ * e₀ + l₁ * e₁ - (M₂ * e₀ - M₁ * e₁),
        M₂ * e₀ - M₁ * e₁, M₂ * l₀ * e₀ - M₁ * l₁ * e₁ -
          (-(M₂ ^ 2 + 2 * q) * e₀ + (M₁ ^ 2 + q) * e₁)⟩ : MixedJet ℝ) := by
    unfold upperGapJet
    dsimp only
    rw [he, heu, hed, heud, hedd]
  have hK : tailBaseJet p u v = ⟨B, B * (b - L), B * w, B * (w * (b - L) + q)⟩ := by
    unfold tailBaseJet
    dsimp only
    rw [hL₁, sub_neg_eq_add]
  have hdu : (separatedMainJet p u v).du =
      B * (r ^ 2 * (b - L) + 2 * r * (s - t) - e₀ * lower₀ + e₁ * lower₁) := by
    unfold separatedMainJet
    dsimp only
    rw [hK, hR, hE]
    dsimp only [MixedJet.add, MixedJet.mul, s, t, lower₀, lower₁]
    ring
  have hduv : (separatedMainJet p u v).duv =
      B * (r ^ 2 * (w * (b - L) + q) +
        2 * r * ((b - L) * t + w * (s - t) + q * f₁ + L₂ * f) +
        2 * (s - t) * t + e₀ * ((M₂ - w) * lower₀ + q) +
        e₁ * ((w - M₁) * lower₁)) := by
    unfold separatedMainJet
    dsimp only
    rw [hK, hR, hE]
    dsimp only [MixedJet.add, MixedJet.mul, s, t, lower₀, lower₁]
    ring
  have hSigns := separatedFour_main_signs hp hu₀ hu₄ hgap
  rw [hdu, hduv]
  exact ⟨mul_pos hB hSigns.1, mul_neg_of_pos_of_neg hB hSigns.2⟩

/-- Hägele's original kernel has strictly negative mixed derivative in the independent
lower and upper coordinates on the central strip with gap at least four. -/
theorem logKernel_central_gap_four_mixed_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₄ : u ≤ 4) (hgap : 4 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let n : ℝ := p + 1
  let N : ℝ := (p + 2).choose 2
  let A := upperTailNormalizer (p + 1) h (N / n)
  let S : ℝ → ℝ := fun y ↦ 1 / Real.sqrt (A y)
  let F := separatedMainJet p
  let Q : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (tailBaseJet p x y).mul (upperGapJet (upperTailQuadratic h) x y)
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp only [h]; positivity
  have hu : 0 < u := by linarith only [hu₀]
  have hd : 0 < d := (by norm_num : (0 : ℝ) < 4).trans_le hgap
  have huv : u < v := sub_pos.mp hd
  have hv : 0 < v := hu.trans huv
  have hv₁ : 1 ≤ v := by linarith
  have ha := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr hv) hpR)
  have hA : 0 < A v := by
    have ha₀ := (Real.exp_pos (-v / (p : ℝ))).le
    have hb : 0 < 1 - (Real.exp (-v / (p : ℝ))) ^ 3 := by
      have H := pow_lt_pow_left₀ ha ha₀ (by decide : 3 ≠ 0)
      simpa using sub_pos.mpr H
    have hw := mul_pos hb (weight_pos hp₀ ha₀ ha)
    rw [upperTail_upper_weight hp₀ hv] at hw
    exact pos_of_mul_pos_right hw (by positivity)
  obtain ⟨s', hs', hS⟩ := upperTail_normalizer_invSqrt hh
    (show 0 ≤ N / n by dsimp only [N, n]; positivity) hv₁ hA
  have hSJ : MixedJet.IsAt (fun _ y ↦ ⟨S y, 0, s', 0⟩) u v :=
    ⟨Filter.Eventually.of_forall (fun y ↦ hasDerivAt_const u (S y)), hS,
      hasDerivAt_const v (0 : ℝ)⟩
  have hR : MixedJet.IsAt
      (upperGapJet (fun x y ↦ 1 - upperTailSlope h y * upperTailRatio h x)) u v :=
    upperGapJet_isAt (tailCorrection_smooth hh hu hd)
  have hE : MixedJet.IsAt (upperGapJet (upperTailLinearError h)) u v :=
    upperGapJet_isAt (tailLinear_smooth hh hu hd)
  have hBase := tailBaseJet_isAt hp₀ hu huv
  have hF : MixedJet.IsAt F u v := hBase.mul ((hR.mul hR).add hE)
  have hQgap : MixedJet.IsAt (upperGapJet (upperTailQuadratic h)) u v :=
    upperGapJet_isAt (tailQuadratic_smooth hh hu hd)
  have hQ : MixedJet.IsAt Q u v := hBase.mul hQgap
  have hSigns := separatedFour_mainJet_signs hp hu₀ hu₄ hgap
  have hMain := upperTail_restore_upperFactor hF hS (one_div_pos.mpr (Real.sqrt_pos.mpr hA))
    hs' hSigns.1.le hSigns.2
  have hRad := separatedFour_radical_mixed_neg hp hu₀ hu₄ hgap
  let J : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (⟨S y, 0, s', 0⟩ : MixedJet ℝ).mul (F x y)
  let K : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (⟨S y, 0, s', 0⟩ : MixedJet ℝ).mul (Q x y)
  have hJ : MixedJet.IsAt J u v := hSJ.mul hF
  have hK : MixedJet.IsAt K u v := hSJ.mul hQ
  have hJvalue (x y : ℝ) : (J x y).value = S y * (F x y).value := rfl
  have hKvalue (x y : ℝ) : (K x y).value = separatedGapRadicalContribution p x y := by
    unfold K Q MixedJet.mul separatedGapRadicalContribution
    dsimp only [upperGapJet, tailBaseJet, S, A, N, n, h]
    ring
  have jet_mixed {T : ℝ → ℝ → MixedJet ℝ} (hT : MixedJet.IsAt T u v) :
      deriv (fun y ↦ deriv (fun x ↦ (T x y).value) u) v = (T u v).duv := by
    have hfirst : (fun y ↦ deriv (fun x ↦ (T x y).value) u) =ᶠ[𝓝 v]
        fun y ↦ (T u y).du := hT.1.mono fun _ hy ↦ hy.deriv
    rw [hfirst.deriv_eq, hT.2.2.deriv]
  have hJneg : (J u v).duv < 0 := by
    rw [← jet_mixed hJ]
    simpa only [hJvalue] using hMain
  have hKneg : (K u v).duv < 0 := by
    rw [← jet_mixed hK]
    simpa only [hKvalue] using hRad
  have hLocal : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      fun y ↦ deriv (fun x ↦ ((J x y).add (K x y)).value) u := by
    filter_upwards [eventually_gt_nhds huv] with y hy
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy] with x hx hxy
    have hk := upperTail_logKernel_decomposition hp₀ hx (sub_pos.mpr hxy)
    dsimp only at hk
    rw [sub_add_cancel y x] at hk
    rw [hk]
    change _ = (J x y).value + (K x y).value
    rw [hJvalue, hKvalue]
    dsimp only [F, S, A, N, n, separatedMainJet, separatedGapRadicalContribution,
      upperGapJet, tailBaseJet, h, MixedJet.mul, MixedJet.add]
    ring
  rw [hLocal.deriv_eq, jet_mixed (hJ.add hK)]
  change (J u v).duv + (K u v).duv < 0
  linarith only [hJneg, hKneg]

#print axioms logKernel_central_gap_four_mixed_lt

end RefinedBMV.PositiveCenter
