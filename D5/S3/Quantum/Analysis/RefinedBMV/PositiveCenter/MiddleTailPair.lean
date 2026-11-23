/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailPair
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed derivative decomposition for the normalized central-gap kernel. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailLinearContribution
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourRadicalSign

/-! Mixed derivatives of the three normalized summands in the separated kernel. -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private tailBaseJet tailBaseJet_isAt tailLinear_smooth tailQuadratic_smooth
  tailCorrection_smooth from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet

/-- The mixed derivative in the independent coordinates inherits the exact
decomposition into the normalized leading, linear and radical contributions. -/
theorem middleTail_kernel_mixed_eq {p : ℕ} (hp₀ : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv₁ : 1 ≤ v) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v =
      deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v +
      deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v +
      deriv (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) v := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let n : ℝ := p + 1
  let N : ℝ := (p + 2).choose 2
  let A := upperTailNormalizer (p + 1) h (N / n)
  let S : ℝ → ℝ := fun y ↦ 1 / Real.sqrt (A y)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp only [h]; positivity
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
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
  let R := upperGapJet (fun x y ↦ 1 - upperTailSlope h y * upperTailRatio h x)
  let W : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (⟨S y, 0, s', 0⟩ : MixedJet ℝ).mul (tailBaseJet p x y)
  let J : ℝ → ℝ → MixedJet ℝ := fun x y ↦ (W x y).mul ((R x y).mul (R x y))
  let L : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (W x y).mul (upperGapJet (upperTailLinearError h) x y)
  let Q : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (W x y).mul (upperGapJet (upperTailQuadratic h) x y)
  have hR : MixedJet.IsAt R u v := upperGapJet_isAt (tailCorrection_smooth hh hu hd)
  have hW : MixedJet.IsAt W u v := hSJ.mul (tailBaseJet_isAt hp₀ hu huv)
  have hJ : MixedJet.IsAt J u v := hW.mul (hR.mul hR)
  have hL : MixedJet.IsAt L u v := hW.mul (upperGapJet_isAt (tailLinear_smooth hh hu hd))
  have hQ : MixedJet.IsAt Q u v := hW.mul (upperGapJet_isAt (tailQuadratic_smooth hh hu hd))
  have hJvalue (x y : ℝ) : (J x y).value = middleTailLeadingContribution p x y := by
    dsimp only [J, W, R, S, A, N, n, h, MixedJet.mul, tailBaseJet, upperGapJet,
      middleTailLeadingContribution]
    ring
  have hLvalue (x y : ℝ) : (L x y).value = middleTailLinearContribution p x y := by
    dsimp only [L, W, S, A, N, n, h, MixedJet.mul, tailBaseJet, upperGapJet,
      middleTailLinearContribution]
    ring
  have hQvalue (x y : ℝ) : (Q x y).value = separatedGapRadicalContribution p x y := by
    dsimp only [Q, W, S, A, N, n, h, MixedJet.mul, tailBaseJet, upperGapJet,
      separatedGapRadicalContribution]
  have jet_mixed {T : ℝ → ℝ → MixedJet ℝ} (hT : MixedJet.IsAt T u v) :
      deriv (fun y ↦ deriv (fun x ↦ (T x y).value) u) v = (T u v).duv := by
    have hfirst : (fun y ↦ deriv (fun x ↦ (T x y).value) u) =ᶠ[𝓝 v]
        fun y ↦ (T u y).du := hT.1.mono fun _ hy ↦ hy.deriv
    rw [hfirst.deriv_eq, hT.2.2.deriv]
  have hLocal : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      fun y ↦ deriv (fun x ↦ (((J x y).add (L x y)).add (Q x y)).value) u := by
    filter_upwards [eventually_gt_nhds huv] with y hy
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy] with x hx hxy
    have hk := upperTail_logKernel_decomposition hp₀ hx (sub_pos.mpr hxy)
    dsimp only at hk
    rw [sub_add_cancel y x] at hk
    rw [hk]
    dsimp only [J, L, Q, W, R, S, A, N, n, h, MixedJet.mul, MixedJet.add, tailBaseJet, upperGapJet]
    ring
  rw [hLocal.deriv_eq, jet_mixed ((hJ.add hL).add hQ)]
  rw [show deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v =
      (J u v).duv by simpa only [hJvalue] using jet_mixed hJ,
    show deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v =
      (L u v).duv by simpa only [hLvalue] using jet_mixed hL,
    show deriv (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) v =
      (Q u v).duv by simpa only [hQvalue] using jet_mixed hQ]
  rfl

end RefinedBMV.PositiveCenter
