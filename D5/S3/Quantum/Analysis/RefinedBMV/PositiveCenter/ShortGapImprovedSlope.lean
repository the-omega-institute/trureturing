/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapImprovedSlope
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-moment improvement of the positive-center short-gap slope on [1,∞). -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapJ
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The fourth-moment argument of `central-middle-gap-proof-pro-20261124.sse`, §3. -/

open Set

noncomputable section

namespace RefinedBMV.PositiveCenter

open SmallCorner
open private spacing scale varianceHalf scale_pos varianceHalf_pos variance_eq
  rawMoment_small rawMoment_ge_four_le U U₁ U₂ rawExp U_majorant_eq_rawExp
  hasSum_U hasSum_rawExp hasSum_realExp slope_square_le from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapJ

private theorem rawMoment_four_le_eleven {p : ℕ} (hp : 0 < p) (hq : spacing p ≤ 3 / 11) :
    shortGapRawMoment p 4 ≤ 11 * compositionMarginalVariance p := by
  obtain ⟨_, _, _, _, h₄⟩ := rawMoment_small hp
  let q := spacing p
  have hq₀ : 0 ≤ q := by
    dsimp [q, spacing]
    positivity
  have hq₂ : q ^ 2 ≤ (3 / 11 : ℝ) ^ 2 := pow_le_pow_left₀ hq₀ hq 2
  rw [h₄, variance_eq hp]
  change (3 + q) * (18 + 12 * q - q ^ 2) / 10 ≤ 11 * ((1 + q) / 2)
  nlinarith only [hq₀, hq₂, show 0 ≤ q ^ 3 by positivity]

private def slopeRatio : ℕ → ℝ
  | 0 => 1
  | 1 => 76 / 99
  | _ + 2 => 77 / 108

private theorem slope_moment_le {p : ℕ} (hp : 11 ≤ p) (n : ℕ) :
    (shortGapRawMoment p (n + 2) - 1) *
        (1 + 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤
      2 * compositionMarginalVariance p * (3 : ℝ) ^ n * slopeRatio n := by
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : spacing p ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  obtain ⟨_, _, h₂, h₃, _⟩ := rawMoment_small hp₀
  let v := compositionMarginalVariance p
  have hv : 0 ≤ v := (compositionMarginalVariance_pos p).le
  match n with
  | 0 => norm_num [slopeRatio, h₂] <;> exact le_of_eq (by ring)
  | 1 =>
    have h := mul_le_mul_of_nonneg_left hq (compositionMarginalVariance_pos p).le
    norm_num [slopeRatio, h₃] <;> nlinarith only [h]
  | n + 2 =>
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hd : (12 : ℝ) ≤ ((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) := by
      nlinarith only [hn, sq_nonneg (n : ℝ)]
    have hf : (2 : ℝ) / (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2)) ≤ 2 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    have hm : shortGapRawMoment p (n + 4) ≤ 11 * v * (3 : ℝ) ^ n :=
      (rawMoment_ge_four_le hp₀ n).trans
        (mul_le_mul_of_nonneg_right (rawMoment_four_le_eleven hp₀ hq) (by positivity))
    simp only [Nat.cast_add, Nat.cast_ofNat]
    change (shortGapRawMoment p (n + 4) - 1) *
        (1 + 2 / (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2))) ≤
      2 * v * (3 : ℝ) ^ (n + 2) * (77 / 108)
    calc
      _ ≤ (11 * v * (3 : ℝ) ^ n) * (1 + 2 / 12) :=
        mul_le_mul (by linarith only [hm]) (add_le_add_right hf 1)
          (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hv) (by positivity))
      _ = _ := by rw [pow_add]; ring

private theorem U_improved_majorant {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 0 < t) :
    U p t + t * U₁ p t + t ^ 2 * U₂ p t / 4 ≤
      scale p * varianceHalf p * ((77 / 108) * Real.exp (3 * t) +
        (31 / 108 + (65 / 396) * t)) := by
  have hp₀ : 0 < p := by omega
  rw [U_majorant_eq_rawExp hp₀]
  let a := scale p * varianceHalf p
  let e (n : ℕ) : ℝ := (3 * t) ^ n / (n.factorial : ℝ)
  let g (n : ℕ) : ℝ := a * slopeRatio n * e n
  have he : HasSum e (Real.exp (3 * t)) := hasSum_realExp (3 * t)
  have hg : HasSum g (a * ((77 / 108) * Real.exp (3 * t) +
      (31 / 108 + (65 / 396) * t))) := by
    apply (hasSum_nat_add_iff' (f := g) 2).1
    have hvalue : a * ((77 / 108) * Real.exp (3 * t) + (31 / 108 + (65 / 396) * t)) -
        (∑ n ∈ Finset.range 2, g n) =
      a * (77 / 108) * (Real.exp (3 * t) - ∑ n ∈ Finset.range 2, e n) := by
      norm_num [g, e, slopeRatio, Finset.sum_range_succ] <;> ring
    rw [hvalue]
    exact ((hasSum_nat_add_iff' (f := e) 2).2 he).mul_left (a * (77 / 108))
  let f (n : ℕ) : ℝ := (scale p * (t ^ n / (n.factorial : ℝ)) / 4) *
    ((shortGapRawMoment p (n + 2) - 1) * (1 + 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))))
  have hl : HasSum f (U p t / 2 + scale p * rawExp p 2 t / 4) := by
    refine (((hasSum_U hp₀ ht).div_const 2).add
      (((hasSum_rawExp p 2 t).mul_left (scale p)).div_const 4)).congr_fun fun n ↦ ?_
    have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    have hfactorial : (((n + 2).factorial : ℕ) : ℝ) =
        (n.factorial : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    change f n = scale p * (shortGapRawMoment p (n + 2) - 1) *
        (t ^ n / ((n + 2).factorial : ℝ)) / 2 +
        scale p * ((shortGapRawMoment p (n + 2) - 1) * (t ^ n / (n.factorial : ℝ))) / 4
    rw [hfactorial]
    dsimp [f]
    field_simp [hfac.ne', hden.ne']
    ring
  rw [← hl.tsum_eq, ← hg.tsum_eq]
  apply Summable.tsum_le_tsum _ hl.summable hg.summable
  intro n
  have h := mul_le_mul_of_nonneg_left (slope_moment_le hp n)
    (show 0 ≤ scale p * (t ^ n / (n.factorial : ℝ)) / 4 from
      div_nonneg (mul_nonneg (scale_pos p).le (by positivity)) (by norm_num))
  refine h.trans_eq ?_
  change _ = a * slopeRatio n * ((3 * t) ^ n / (n.factorial : ℝ))
  rw [mul_pow]
  dsimp [a, varianceHalf]
  ring

private theorem improved_slope_scalar {t : ℝ} (ht : 1 ≤ t) :
    (77 / 108) * Real.exp (3 * t) + (31 / 108 + (65 / 396) * t) ≤
      (43 / 50 : ℝ) ^ 2 * Real.exp (3 * t) := by
  let f (x : ℝ) : ℝ := Real.exp (-3 * x) * (31 / 108 + (65 / 396) * x)
  have hd (x : ℝ) : HasDerivAt f
      (Real.exp (-3 * x) * (65 / 396 - 3 * (31 / 108 + (65 / 396) * x))) x := by
    exact ((((hasDerivAt_id' x).const_mul (-3 : ℝ)).exp).mul
      (((hasDerivAt_id' x).const_mul (65 / 396 : ℝ)).const_add (31 / 108))).congr_deriv (by ring)
  have hdiff : Differentiable ℝ f := fun x ↦ (hd x).differentiableAt
  have hanti : AntitoneOn f (Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn fun x hx ↦ ?_
    have hx₀ : x ∈ Ici (0 : ℝ) := interior_subset hx
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (by linarith only [mem_Ici.mp hx₀])
  have he : (20 : ℝ) < Real.exp 3 := by
    have hTaylor := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
    exact (by norm_num : (20 : ℝ) < 89641 / 4480).trans_le hTaylor
  have hf : f t ≤ (43 / 50 : ℝ) ^ 2 - 77 / 108 := calc
    f t ≤ f 1 := hanti (show (0 : ℝ) ≤ 1 by norm_num) (zero_le_one.trans ht) ht
    _ = (134 / 297 : ℝ) / Real.exp 3 := by
      simp only [f, mul_one, Real.exp_neg, div_eq_mul_inv]
      ring
    _ ≤ (134 / 297 : ℝ) / 20 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he.le
    _ ≤ _ := by norm_num
  have h := mul_le_mul_of_nonneg_right hf (Real.exp_pos (3 * t)).le
  have hcancel : f t * Real.exp (3 * t) = 31 / 108 + (65 / 396) * t := calc
    _ = (31 / 108 + (65 / 396) * t) * (Real.exp (-3 * t) * Real.exp (3 * t)) := by
      dsimp [f]
      ring
    _ = _ := by rw [← Real.exp_add, show -3 * t + 3 * t = 0 by ring, Real.exp_zero, mul_one]
  rw [hcancel] at h
  linarith only [h]

/-- The positive-center marginal slope gains a uniform factor of `43/50` for gaps at least one. -/
theorem shortGapJ_deriv_le_from_one {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 1 ≤ t) :
    deriv (shortGapJ p) t ≤
      (43 / 50) *
        Real.sqrt ((3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) * (1 + 3 / (p : ℝ)) / 8) *
        Real.exp (3 * t / 2) := by
  have hp₀ : 0 < p := by omega
  have hc : 0 ≤ scale p * varianceHalf p := (mul_pos (scale_pos p) (varianceHalf_pos p)).le
  have hconstant : scale p * varianceHalf p =
      (3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) * (1 + 3 / (p : ℝ)) / 8 := by
    unfold varianceHalf scale spacing
    rw [variance_eq hp₀]
    ring
  rw [← hconstant]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hc, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (3 * t / 2) = 3 * t by ring]
  calc
    _ ≤ _ := slope_square_le hp₀ t
    _ ≤ _ := U_improved_majorant hp (zero_lt_one.trans_le ht)
    _ ≤ scale p * varianceHalf p * ((43 / 50 : ℝ) ^ 2 * Real.exp (3 * t)) :=
      mul_le_mul_of_nonneg_left (improved_slope_scalar ht) hc
    _ = _ := by ring

end RefinedBMV.PositiveCenter
