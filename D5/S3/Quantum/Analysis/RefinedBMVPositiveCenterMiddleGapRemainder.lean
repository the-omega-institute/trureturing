/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMiddleGapRemainder
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convexity of the square root remainder in the positive-center gap profile. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterCompactGap
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMiddleGapFirstOrder
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Convexity of the omitted square root terms -/

open Filter Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

private abbrev gapDomain := Ioi (2 : ℝ)

private structure GapDecay (f : ℝ → ℝ) : Prop where
  nonneg : ∀ t ∈ gapDomain, 0 ≤ f t
  antitone : AntitoneOn f gapDomain
  convex : ConvexOn ℝ gapDomain f

private theorem GapDecay.add {f g : ℝ → ℝ} (hf : GapDecay f) (hg : GapDecay g) :
    GapDecay (fun t ↦ f t + g t) :=
  ⟨fun t ht ↦ add_nonneg (hf.nonneg t ht) (hg.nonneg t ht),
    fun _ hs _ ht hst ↦ add_le_add (hf.antitone hs ht hst) (hg.antitone hs ht hst),
    hf.convex.add hg.convex⟩

private theorem GapDecay.mul {f g : ℝ → ℝ} (hf : GapDecay f) (hg : GapDecay g) :
    GapDecay (fun t ↦ f t * g t) :=
  ⟨fun t ht ↦ mul_nonneg (hf.nonneg t ht) (hg.nonneg t ht),
    fun s hs t ht hst ↦ mul_le_mul (hf.antitone hs ht hst) (hg.antitone hs ht hst)
      (hg.nonneg t ht) (hf.nonneg s hs),
    hf.convex.mul hg.convex hf.nonneg hg.nonneg (hf.antitone.monovaryOn hg.antitone)⟩

private theorem GapDecay.const {k : ℝ} (hk : 0 ≤ k) : GapDecay (fun _ ↦ k) :=
  ⟨fun _ _ ↦ hk, fun _ _ _ _ _ ↦ le_rfl, convexOn_const k (convex_Ioi _)⟩

private theorem GapDecay.scale {f : ℝ → ℝ} (hf : GapDecay f) {k : ℝ} (hk : 0 ≤ k) :
    GapDecay (fun t ↦ k * f t) := (GapDecay.const hk).mul hf

private theorem GapDecay.pow {f : ℝ → ℝ} (hf : GapDecay f) (k : ℕ) :
    GapDecay (fun t ↦ f t ^ k) := by
  induction k with
  | zero => simpa using GapDecay.const (show (0 : ℝ) ≤ 1 by norm_num)
  | succ k hk => simpa only [pow_succ] using hk.mul hf

private theorem GapDecay.congr {f g : ℝ → ℝ} (hf : GapDecay f) (heq : EqOn f g gapDomain) :
    GapDecay g :=
  ⟨fun t ht ↦ heq ht ▸ hf.nonneg t ht,
    fun _ hs _ ht hst ↦ heq hs ▸ heq ht ▸ hf.antitone hs ht hst,
    hf.convex.congr heq⟩

private theorem GapDecay.of_derivatives {f : ℝ → ℝ}
    (hf : ∀ t ∈ gapDomain, ContDiffAt ℝ 2 f t)
    (hn : ∀ t ∈ gapDomain, 0 ≤ f t)
    (hd : ∀ t ∈ gapDomain, deriv f t ≤ 0)
    (hdd : ∀ t ∈ gapDomain, 0 ≤ deriv (deriv f) t) : GapDecay f := by
  have h₁ : DifferentiableOn ℝ f gapDomain :=
    fun t ht ↦ ((hf t ht).differentiableAt (by norm_num)).differentiableWithinAt
  have h₂ : DifferentiableOn ℝ (deriv f) gapDomain := by
    intro t ht
    exact (((hf t ht).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero)
      |>.differentiableWithinAt
  refine ⟨hn, antitoneOn_of_deriv_nonpos (convex_Ioi _) h₁.continuousOn ?_ ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _) h₁ h₂ hdd⟩
  · simpa only [interior_Ioi] using h₁
  · simpa only [interior_Ioi] using hd

private theorem hasDerivAt_gapDecayExp (rate t : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-(rate * x))) (-rate * Real.exp (-(rate * t))) t := by
  convert (((hasDerivAt_id' t).const_mul rate).neg.exp) using 1 <;> simp <;> ring

private theorem gapDecay_gapPow_mul_exp {h : ℝ} (hh : 0 < h) (n : ℕ) (hn : n ≤ 4)
    {rate : ℝ} (hrate : (n : ℝ) / 2 + 1 ≤ rate) :
    GapDecay (fun t ↦ upperTailGap h t ^ n * Real.exp (-(rate * t))) := by
  let a := upperTailGap h
  let L := upperTailSlope h
  let f : ℝ → ℝ := fun t ↦ a t ^ n * Real.exp (-(rate * t))
  have ha {t : ℝ} (ht : 0 < t) : 0 < a t := by
    change 0 < upperTailGap h t
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hf {t : ℝ} (ht : 0 < t) : 0 ≤ f t :=
    mul_nonneg (pow_nonneg (ha ht).le n) (Real.exp_pos _).le
  have hd {t : ℝ} (ht : 0 < t) :
      HasDerivAt f (((n : ℝ) * L t - rate) * f t) t := by
    have hdA : HasDerivAt a (L t * a t) t := by
      have h := hasDerivAt_upperTailGap (t := t) hh
      refine h.congr_deriv ?_
      have hlog := upperTailGap_logDeriv hh ht
      rw [h.deriv] at hlog
      exact (div_eq_iff (ha ht).ne').mp hlog
    have hdN : HasDerivAt (fun s ↦ a s ^ n) ((n : ℝ) * L t * a t ^ n) t := by
      refine (hdA.pow n).congr_deriv ?_
      cases n with
      | zero => simp
      | succ n => simp only [Nat.add_one_sub_one, pow_succ]; ring
    refine (hdN.fun_mul (hasDerivAt_gapDecayExp rate t)).congr_deriv ?_
    dsimp only [f]
    ring
  have hdd {t : ℝ} (ht : 0 < t) : deriv (deriv f) t =
      (((n : ℝ) * L t - rate)^2 + (n : ℝ) * deriv L t) * f t := by
    have heq : deriv f =ᶠ[𝓝 t] fun s ↦ ((n : ℝ) * L s - rate) * f s := by
      filter_upwards [eventually_gt_nhds ht] with s hs using (hd hs).deriv
    have hL := hasDerivAt_upperTailSlope hh ht
    rw [heq.deriv_eq, (((hL.const_mul (n : ℝ)).sub_const rate).fun_mul (hd ht)).deriv]
    rw [hL.deriv]
    ring
  have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  refine GapDecay.of_derivatives (f := f) (fun t _ ↦ ?_) (fun t ht ↦ ?_) ?_ ?_
  · unfold f a upperTailGap
    fun_prop
  · exact hf ((by norm_num : (0 : ℝ) < 2).trans ht)
  · intro t ht
    have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
    have hLhalf := (upperTailSlope_bounds hh ht₀).2.1.trans
      (one_div_le_one_div_of_le (by norm_num) ht.le)
    have hmul := mul_le_mul_of_nonneg_left hLhalf (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [(hd ht₀).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hmul, hrate]) (hf ht₀)
  · intro t ht
    have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
    have hL := upperTailSlope_bounds hh ht₀
    have hLhalf : L t ≤ 1 / 2 := hL.2.1.trans
      (one_div_le_one_div_of_le (by norm_num) ht.le)
    have ht_sq : (4 : ℝ) ≤ t ^ 2 := by
      convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ht.le 2 using 1 <;> norm_num
    have hLsq : -deriv L t ≤ 1 / 4 := hL.2.2.2.1.trans
      (one_div_le_one_div_of_le (by norm_num) ht_sq)
    have hm := mul_le_mul_of_nonneg_left hLhalf (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hmul := mul_le_mul_of_nonneg_left hLsq (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hdiff : 1 ≤ rate - (n : ℝ) * L t := by linarith only [hrate, hm]
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdiff 2
    rw [hdd ht₀]
    exact mul_nonneg (by nlinarith only [hsquare, hmul, hn']) (hf ht₀)

private theorem gap_pos_of_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailGap h t := by
  rw [expGapMean_eq hh]
  exact mul_pos ht (expGapMean_pos _ _)

private theorem gapDecay_one_div_gap {h : ℝ} (hh : 0 < h) :
    GapDecay (fun t ↦ 1 / upperTailGap h t) := by
  have hL : GapDecay (upperTailSlope h) := by
    refine GapDecay.of_derivatives (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      (fun t ht ↦ ?_)
    · have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
      have he : Real.exp (h * t) - 1 ≠ 0 :=
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh ht₀))).ne'
      unfold upperTailSlope
      exact contDiffAt_const.div (by fun_prop) he
    · exact (upperTailSlope_bounds hh ((by norm_num : (0 : ℝ) < 2).trans ht)).1.le
    · exact neg_nonneg.mp
        (upperTailSlope_bounds hh ((by norm_num : (0 : ℝ) < 2).trans ht)).2.2.1
    · exact (upperTailSlope_bounds hh ((by norm_num : (0 : ℝ) < 2).trans ht)).2.2.2.2.1
  apply ((GapDecay.const hh.le).add hL).congr
  intro t ht
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
  have ha := gap_pos_of_pos hh ht₀
  have hgap : h * upperTailGap h t = 1 - Real.exp (-(h * t)) := by
    unfold upperTailGap
    field_simp [hh.ne']
  change h + upperTailSlope h t = 1 / upperTailGap h t
  rw [← upperTailGap_logDeriv hh ht₀, (hasDerivAt_upperTailGap (t := t) hh).deriv]
  field_simp [ha.ne']
  linarith only [hgap]

private theorem gapDecay_lambda {h : ℝ} (hh : 0 < h) : GapDecay (upperTailLambda h) := by
  let g : ℝ := 3 + h
  let c : ℝ := g * (3 + 2 * h) / 2
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hc : 0 ≤ c := by dsimp [c, g]; positivity
  have h₀ := gapDecay_gapPow_mul_exp hh 0 (by decide) (rate := g) (by dsimp [g]; linarith)
  have h₁ := gapDecay_gapPow_mul_exp hh 1 (by decide) (rate := g) (by dsimp [g]; linarith)
  have h₂ := gapDecay_gapPow_mul_exp hh 2 (by decide) (rate := 2) (by norm_num)
  refine ((h₀.add (h₁.scale hg)).add (h₂.scale hc)).congr ?_
  intro t _
  unfold upperTailLambda
  dsimp only [g, c]
  ring

private theorem gapDecay_scaledLambdaSq {h : ℝ} (hh : 0 < h) :
    GapDecay (fun t ↦ Real.exp (3 * t / 2) / upperTailGap h t * upperTailLambda h t ^ 2) := by
  let g : ℝ := 3 + h
  let c : ℝ := g * (3 + 2 * h) / 2
  let l₁ : ℝ := 2 * g - 3 / 2
  let l₂ : ℝ := g + 1 / 2
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hc : 0 ≤ c := by dsimp [c, g]; positivity
  have h₀ := gapDecay_gapPow_mul_exp hh 0 (by decide) (rate := l₁) (by dsimp [l₁, g]; linarith)
  have h₁ := gapDecay_gapPow_mul_exp hh 1 (by decide) (rate := l₁) (by dsimp [l₁, g]; linarith)
  have h₂ := gapDecay_gapPow_mul_exp hh 1 (by decide) (rate := l₂) (by dsimp [l₂, g]; linarith)
  have h₃ := gapDecay_gapPow_mul_exp hh 2 (by decide) (rate := l₂) (by dsimp [l₂, g]; linarith)
  have h₄ := gapDecay_gapPow_mul_exp hh 3 (by decide) (rate := 5 / 2) (by norm_num)
  have h₅ := (gapDecay_one_div_gap hh).mul h₀
  refine (((((h₅.add (h₀.scale (by positivity : 0 ≤ 2 * g))).add
    (h₁.scale (sq_nonneg g))).add (h₂.scale (by positivity : 0 ≤ 2 * c))).add
    (h₃.scale (by positivity : 0 ≤ 2 * g * c))).add (h₄.scale (sq_nonneg c))).congr ?_
  intro t ht
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
  have ha := (gap_pos_of_pos hh ht₀).ne'
  have he₁ : Real.exp (-(l₁ * t)) = Real.exp (3 * t / 2) * Real.exp (-(g * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add (-(g * t)) (-(g * t)), ← Real.exp_add]
    congr 1
    dsimp [l₁]
    ring
  have he₂ : Real.exp (-(l₂ * t)) =
      Real.exp (3 * t / 2) * Real.exp (-(g * t)) * Real.exp (-(2 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [l₂]
    ring
  have he₃ : Real.exp (-((5 / 2 : ℝ) * t)) = Real.exp (3 * t / 2) * Real.exp (-(2 * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add (-(2 * t)) (-(2 * t)), ← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [he₁, he₂, he₃]
  change _ = Real.exp (3 * t / 2) / upperTailGap h t *
    ((1 + g * upperTailGap h t) * Real.exp (-(g * t)) +
      c * upperTailGap h t ^ 2 * Real.exp (-(2 * t))) ^ 2
  field_simp [ha]
  ring

private theorem one_sub_lambda_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < 1 - upperTailLambda h t := by
  rw [one_sub_upperTailLambda_eq_collisionRadicand hh]
  exact mul_pos (by positivity) (collisionRadicand_pos h t)

private noncomputable def rootReciprocal (h t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - upperTailLambda h t))⁻¹

private theorem gapDecay_rootReciprocal {h : ℝ} (hh : 0 < h) :
    GapDecay (rootReciprocal h) := by
  let f : ℝ → ℝ := fun t ↦ 1 - upperTailLambda h t
  let j : ℝ → ℝ := fun t ↦ Real.sqrt (f t) + 1
  have hf := gapDecay_lambda hh
  have hfc : ConcaveOn ℝ gapDomain f := by
    convert hf.convex.neg.add_const (1 : ℝ) using 1
    funext t
    simp [f, sub_eq_add_neg, add_comm]
  have hf₀ {t : ℝ} (ht : t ∈ gapDomain) : 0 ≤ f t :=
    (one_sub_lambda_pos hh ((by norm_num : (0 : ℝ) < 2).trans ht)).le
  have hsqrt : ConcaveOn ℝ gapDomain (Real.sqrt ∘ f) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro s hs t ht a b ha hb hab
    exact ((Real.strictConcaveOn_sqrt.concaveOn).2 (hf₀ hs) (hf₀ ht) ha hb hab).trans
      (Real.sqrt_le_sqrt (hfc.2 hs ht ha hb hab))
  have hj : ConcaveOn ℝ gapDomain j := hsqrt.add_const 1
  have hmono : MonotoneOn j gapDomain := by
    intro s hs t ht hst
    simpa only [j, f, add_comm] using
      add_le_add_right (Real.sqrt_le_sqrt (sub_le_sub_left (hf.antitone hs ht hst) 1)) 1
  have hj₀ (t : ℝ) : 0 < j t := by dsimp [j]; positivity
  have hinv : ConvexOn ℝ (Ioi (0 : ℝ)) fun t : ℝ ↦ t⁻¹ := by
    simpa using (convexOn_zpow (𝕜 := ℝ) (-1))
  have hcv : ConvexOn ℝ gapDomain (Inv.inv ∘ j) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro s hs t ht a b ha hb hab
    have hp : 0 < a • j s + b • j t := (convex_Ioi (0 : ℝ)) (hj₀ s) (hj₀ t) ha hb hab
    exact (inv_anti₀ hp (hj.2 hs ht ha hb hab)).trans
      (hinv.2 (hj₀ s) (hj₀ t) ha hb hab)
  refine ⟨fun _ _ ↦ by unfold rootReciprocal; positivity, ?_, ?_⟩
  · intro s hs t ht hst
    simpa [rootReciprocal, j, f, add_comm] using inv_anti₀ (hj₀ s) (hmono hs ht hst)
  · exact hcv.congr (fun t _ ↦ by simp only [rootReciprocal, Function.comp_def, j, f, add_comm])

noncomputable def middleGapRootTaylorFive (x : ℝ) : ℝ :=
  x / 2 + x ^ 2 / 8 + x ^ 3 / 16 + 5 * x ^ 4 / 128 + 7 * x ^ 5 / 256

private noncomputable def rootTaylorFiveQuotient (x : ℝ) : ℝ :=
  7 / 256 * x ^ 2 + 7 / 128 * x ^ 3 + 9 / 128 * x ^ 4 + 1 / 16 * x ^ 5 + 1 / 32 * x ^ 6

private theorem sqrt_sub_linear {x : ℝ} (hx : x ≤ 1) :
    1 - Real.sqrt (1 - x) - x / 2 = x ^ 2 * ((1 + Real.sqrt (1 - x))⁻¹ ^ 2 / 2) := by
  let s := Real.sqrt (1 - x)
  have hs : s ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hd : 1 + s ≠ 0 := by positivity
  change 1 - s - x / 2 = x ^ 2 * ((1 + s)⁻¹ ^ 2 / 2)
  rw [show x = 1 - s ^ 2 by linarith only [hs]]
  field_simp [hd]
  ring

private theorem sqrt_sub_order_five {x : ℝ} (hx : x ≤ 1) :
    1 - Real.sqrt (1 - x) - middleGapRootTaylorFive x =
      x ^ 6 * rootTaylorFiveQuotient ((1 + Real.sqrt (1 - x))⁻¹) := by
  let s := Real.sqrt (1 - x)
  have hs : s ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hd : 1 + s ≠ 0 := by positivity
  change 1 - s - middleGapRootTaylorFive x = x ^ 6 * rootTaylorFiveQuotient ((1 + s)⁻¹)
  rw [show x = 1 - s ^ 2 by linarith only [hs]]
  unfold middleGapRootTaylorFive rootTaylorFiveQuotient
  field_simp [hd]
  ring

/-- The omitted terms after the first root coefficient in the scaled gap profile. -/
noncomputable def middleGapRootRemainderOne (h t : ℝ) : ℝ :=
  Real.exp (3 * t / 2) / upperTailGap h t *
    (1 - Real.sqrt (1 - upperTailLambda h t) - upperTailLambda h t / 2)

/-- The omitted terms after the first five root coefficients in the scaled gap profile. -/
noncomputable def middleGapRootRemainderFive (h t : ℝ) : ℝ :=
  Real.exp (3 * t / 2) / upperTailGap h t *
    (1 - Real.sqrt (1 - upperTailLambda h t) - middleGapRootTaylorFive (upperTailLambda h t))

private theorem gapDecay_remainderOne {h : ℝ} (hh : 0 < h) :
    GapDecay (middleGapRootRemainderOne h) := by
  have hF := gapDecay_scaledLambdaSq hh
  have hR := (gapDecay_rootReciprocal hh).pow 2 |>.scale (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  refine (hF.mul hR).congr ?_
  intro t ht
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
  have hX := (one_sub_lambda_pos hh ht₀).le
  unfold middleGapRootRemainderOne
  rw [sqrt_sub_linear (sub_nonneg.mp hX)]
  unfold rootReciprocal
  ring

private theorem gapDecay_remainderFive {h : ℝ} (hh : 0 < h) :
    GapDecay (middleGapRootRemainderFive h) := by
  have hF := (gapDecay_scaledLambdaSq hh).mul ((gapDecay_lambda hh).pow 4)
  have hR := gapDecay_rootReciprocal hh
  have h₂ := (hR.pow 2).scale (show (0 : ℝ) ≤ 7 / 256 by norm_num)
  have h₃ := (hR.pow 3).scale (show (0 : ℝ) ≤ 7 / 128 by norm_num)
  have h₄ := (hR.pow 4).scale (show (0 : ℝ) ≤ 9 / 128 by norm_num)
  have h₅ := (hR.pow 5).scale (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  have h₆ := (hR.pow 6).scale (show (0 : ℝ) ≤ 1 / 32 by norm_num)
  refine (hF.mul ((((h₂.add h₃).add h₄).add h₅).add h₆)).congr ?_
  intro t ht
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
  have hX := (one_sub_lambda_pos hh ht₀).le
  unfold middleGapRootRemainderFive
  rw [sqrt_sub_order_five (sub_nonneg.mp hX)]
  unfold rootTaylorFiveQuotient rootReciprocal
  ring

private theorem GapDecay.signs {f : ℝ → ℝ} (hf : GapDecay f)
    (hd : ∀ t ∈ gapDomain, DifferentiableAt ℝ f t) {t : ℝ} (ht : 2 < t) :
    deriv f t ≤ 0 ∧ 0 ≤ deriv (deriv f) t := by
  have hmem : gapDomain ∈ 𝓝 t := Ioi_mem_nhds ht
  rw [← derivWithin_of_mem_nhds hmem, ← derivWithin_of_mem_nhds hmem (f := deriv f)]
  exact ⟨hf.antitone.derivWithin_nonpos, (hf.convex.monotoneOn_deriv hd).derivWithin_nonneg⟩

private theorem gapRootRemainder_contDiffAt {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    {B : ℝ → ℝ} (hB : ContDiff ℝ 2 B) :
    ContDiffAt ℝ 2 (fun x ↦ Real.exp (3 * x / 2) / upperTailGap h x *
      (1 - Real.sqrt (1 - upperTailLambda h x) - B (upperTailLambda h x))) t := by
  have ha : ContDiffAt ℝ 2 (upperTailGap h) t := by unfold upperTailGap; fun_prop
  have hx : ContDiffAt ℝ 2 (upperTailLambda h) t := by
    unfold upperTailLambda upperTailGap
    fun_prop
  have hs := ((contDiffAt_const (c := (1 : ℝ))).sub hx).sqrt
    (one_sub_lambda_pos hh ht).ne'
  exact ((by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ ↦ Real.exp (3 * x / 2)) t).div
    ha (gap_pos_of_pos hh ht).ne').mul
      (((contDiffAt_const (c := (1 : ℝ))).sub hs).sub (hB.contDiffAt.comp t hx))

/-- The first root truncation underestimates the curvature and the negative slope. -/
theorem middleGapRootRemainderOne_signs {h t : ℝ} (hh : 0 < h) (ht : 2 < t) :
    deriv (middleGapRootRemainderOne h) t ≤ 0 ∧
      0 ≤ deriv (deriv (middleGapRootRemainderOne h)) t := by
  apply (gapDecay_remainderOne hh).signs _ ht
  intro x hx
  exact (gapRootRemainder_contDiffAt hh ((by norm_num : (0 : ℝ) < 2).trans hx)
    (B := fun x ↦ x / 2) (by fun_prop)).differentiableAt (by norm_num)

/-- The five-term root truncation underestimates the curvature and the negative slope. -/
theorem middleGapRootRemainderFive_signs {h t : ℝ} (hh : 0 < h) (ht : 2 < t) :
    deriv (middleGapRootRemainderFive h) t ≤ 0 ∧
      0 ≤ deriv (deriv (middleGapRootRemainderFive h)) t := by
  apply (gapDecay_remainderFive hh).signs _ ht
  intro x hx
  exact (gapRootRemainder_contDiffAt hh ((by norm_num : (0 : ℝ) < 2).trans hx)
    (B := middleGapRootTaylorFive) (by unfold middleGapRootTaylorFive; fun_prop)).differentiableAt
      (by norm_num)

private theorem middleGapProfile_eq_scaled {h t : ℝ} :
    CompactGap.middleGapProfile h t =
      Real.exp (3 * t / 2) / upperTailGap h t *
        (1 - Real.exp (-((3 + h) * t)) - Real.sqrt (1 - upperTailLambda h t)) := by
  change (Real.exp (3 * t / 2) * (1 - Real.exp (-((3 + h) * t))) / upperTailGap h t -
    Real.exp (-((3 / 2 + h) * t)) / 4 -
    Real.exp (3 * t / 2) * Real.sqrt (1 - upperTailLambda h t) / upperTailGap h t) +
    Real.exp (-((3 / 2 + h) * t)) / 4 = _
  ring

private theorem middleGapProfile_eq_firstOrder_add {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    CompactGap.middleGapProfile h t = middleGapFirstOrder h t + middleGapRootRemainderOne h t := by
  have ha := (gap_pos_of_pos hh ht).ne'
  have hE₁ : Real.exp (3 * t / 2) * Real.exp (-((3 + h) * t)) =
      Real.exp (-((3 / 2 + h) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE₂ : Real.exp (3 * t / 2) * Real.exp (-(2 * t)) = Real.exp (-(1 / 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [middleGapProfile_eq_scaled]
  unfold middleGapFirstOrder middleGapRootRemainderOne upperTailLambda
  change _ = ((3 + h) * (3 + 2 * h) / 2) / 2 * upperTailGap h t * Real.exp (-(1 / 2 * t)) +
    1 / 2 * Real.exp (-((3 / 2 + h) * t)) * (3 + h - 1 / upperTailGap h t) + _
  rw [← hE₁, ← hE₂]
  field_simp [ha]
  ring

private theorem derivs_of_sum {F A B : ℝ → ℝ} (hEq : ∀ t > 0, F t = A t + B t)
    (hA : ∀ t > 0, ContDiffAt ℝ 2 A t) (hB : ∀ t > 0, ContDiffAt ℝ 2 B t)
    {t : ℝ} (ht : 0 < t) :
    deriv F t = deriv A t + deriv B t ∧
      deriv (deriv F) t = deriv (deriv A) t + deriv (deriv B) t := by
  have h₁ (s : ℝ) (hs : 0 < s) : deriv F s = deriv A s + deriv B s := by
    have he : F =ᶠ[𝓝 s] fun x ↦ A x + B x := by
      filter_upwards [eventually_gt_nhds hs] with x hx using hEq x hx
    rw [he.deriv_eq]
    exact (((hA s hs).differentiableAt (by norm_num)).hasDerivAt.fun_add
      ((hB s hs).differentiableAt (by norm_num)).hasDerivAt).deriv
  refine ⟨h₁ t ht, ?_⟩
  have he : deriv F =ᶠ[𝓝 t] fun x ↦ deriv A x + deriv B x := by
    filter_upwards [eventually_gt_nhds ht] with x hx using h₁ x hx
  rw [he.deriv_eq]
  have ha := ((hA t ht).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hb := ((hB t ht).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact (ha.hasDerivAt.fun_add hb.hasDerivAt).deriv

open CompactGap

/-- A positive-center block has a strictly negative mixed derivative for every gap at least four. -/
theorem logKernel_mixed_of_four_le {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (hd : 4 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  have hpR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hd₀ : 0 < d := (by norm_num : (0 : ℝ) < 4).trans_le hd
  have hA (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 2 (middleGapFirstOrder h) t := by
    have ha : ContDiffAt ℝ 2 (upperTailGap h) t := by unfold upperTailGap; fun_prop
    have hane : upperTailGap h t ≠ 0 := (gap_pos_of_pos hh ht).ne'
    unfold middleGapFirstOrder
    fun_prop (disch := assumption)
  have hB (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 2 (middleGapRootRemainderOne h) t :=
    gapRootRemainder_contDiffAt hh ht (B := fun x ↦ x / 2) (by fun_prop)
  obtain ⟨h₁, h₂⟩ := derivs_of_sum (fun _ ht ↦ middleGapProfile_eq_firstOrder_add hh ht)
    hA hB hd₀
  obtain ⟨hb₁, hb₂⟩ := middleGapRootRemainderOne_signs hh ((by norm_num : (2 : ℝ) < 4).trans_le hd)
  refine logKernel_middleGap_mixed_of_recentered hp hu ((by norm_num : (2 : ℝ) ≤ 4).trans hd) ?_ ?_
  · change middleGapSlopeBudget h d ≤ -deriv (CompactGap.middleGapProfile h) d
    rw [h₁]
    linarith only [middleGapSlopeBudget_le_neg_deriv_middleGapFirstOrder hh hhmax hd, hb₁]
  · change 0 < deriv (deriv (CompactGap.middleGapProfile h)) d
    rw [h₂]
    exact add_pos_of_pos_of_nonneg (deriv_deriv_middleGapFirstOrder_pos hh hhmax hd) hb₂

#print axioms middleGapRootRemainderOne_signs
#print axioms middleGapRootRemainderFive_signs
#print axioms logKernel_mixed_of_four_le

end RefinedBMV.PositiveCenter
