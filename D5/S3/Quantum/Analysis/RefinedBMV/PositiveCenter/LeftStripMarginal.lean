/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripMarginal
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative-marginal slopes for the separated positive-center strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Bounds on the negative marginal of the separated left strip -/

open MeasureTheory Set

noncomputable section

namespace RefinedBMV.PositiveCenter

open DimThree (gaps mem_gaps_iff_total word_counts_all)
open SmallCorner

private abbrev Gap := ℕ × ℕ × ℕ
private abbrev centered (p : ℕ) (g : Gap) : ℝ := 3 * (g.2.2 : ℝ) / p - 1

private theorem centered_bounds {p : ℕ} (hp : 0 < p) {g : Gap} (hg : g ∈ gaps p) :
    -1 ≤ centered p g ∧ centered p g ≤ 2 := by
  have htotal := (mem_gaps_iff_total p g).mp hg
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hjR : (g.2.2 : ℝ) ≤ p := by exact_mod_cast (show g.2.2 ≤ p by omega)
  have hlow : (0 : ℝ) ≤ 3 * (g.2.2 : ℝ) / p := by positivity
  have hupp : 3 * (g.2.2 : ℝ) / p ≤ 3 := (div_le_iff₀ hpR).2 (by linarith)
  dsimp only [centered]
  constructor <;> linarith

private theorem exp_half_le : Real.exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have h : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]

private theorem exp_quadratic_with_signed_remainder (z : ℝ) :
    ∃ w ≤ max 0 z, Real.exp z = 1 + z + z ^ 2 / 2 + z ^ 3 / 6 * Real.exp w := by
  by_cases hz : z = 0
  · subst z
    exact ⟨0, le_max_left _ _, by simp⟩
  have hdiff : ContDiffOn ℝ ((2 : ℕ) + 1) Real.exp (uIcc 0 z) :=
    Real.contDiff_exp.contDiffOn
  have hne : (0 : ℝ) ≠ z := Ne.symm hz
  obtain ⟨w, hw, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hdiff
  have hexp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hwithin (n : ℕ) : iteratedDerivWithin n Real.exp (uIcc 0 z) 0 = Real.exp 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      Real.contDiff_exp.contDiffAt (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 z), hexp]
  rw [uIoo] at hw
  refine ⟨w, hw.2.le, ?_⟩
  norm_num [taylor_within_apply, Finset.sum_range_succ, hwithin, hexp, Nat.factorial,
    smul_eq_mul] at h
  linarith only [h]

private theorem weighted_exp_lower {y u s : ℝ} (hy₀ : -1 ≤ y) (hy₂ : y ≤ 2)
    (hu : 0 ≤ u) (hu₂ : u ≤ 1 / 2) (hs : s ∈ Icc (0 : ℝ) 1) :
    y ^ 3 * ((1 - s) * s) - (y ^ 4 / 2) * ((1 - s) * s ^ 2) +
        (u ^ 2 * y ^ 5 / 2) * ((1 - s) * s ^ 3) -
        (5 * y ^ 4 / 36) * ((1 - s) * s ^ 4) ≤
      y ^ 2 * ((1 - s) * (y * s) ^ (1 : ℕ) * Real.exp (-u * (y * s))) := by
  have hz : -u * (y * s) ≤ 1 / 2 := by
    have hys : -s ≤ y * s := by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hy₀ hs.1
    have hsu : u * s ≤ u := by simpa using mul_le_mul_of_nonneg_left hs.2 hu
    calc
      -u * (y * s) ≤ -u * (-s) :=
        mul_le_mul_of_nonpos_left hys (neg_nonpos.mpr hu)
      _ ≤ 1 / 2 := by linarith
  obtain ⟨w, hw, he⟩ := exp_quadratic_with_signed_remainder (-u * (y * s))
  have hew : Real.exp w ≤ 5 / 3 :=
    (Real.exp_le_exp.mpr (hw.trans (max_le (by norm_num) hz))).trans exp_half_le
  have hy6 : y ^ 6 ≤ 4 * y ^ 4 := by
    have hsq : y ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (show 0 ≤ y + 2 by linarith) (sub_nonneg.mpr hy₂)]
    calc
      y ^ 6 = y ^ 2 * y ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (by positivity)
  have hu3 : u ^ 3 ≤ (1 / 8 : ℝ) := by
    simpa only [show (1 / 2 : ℝ) ^ 3 = 1 / 8 by norm_num] using pow_le_pow_left₀ hu hu₂ 3
  have hrem : u ^ 3 * y ^ 6 * Real.exp w / 6 ≤ 5 * y ^ 4 / 36 := by
    calc
      _ ≤ (1 / 8 : ℝ) * (4 * y ^ 4) * (5 / 3) / 6 := by gcongr
      _ = _ := by ring
  rw [he]
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hu₂ (show 0 ≤ y ^ 4 by positivity))
    (show 0 ≤ (1 - s) * s ^ 2 by exact mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _))
  have h₄ := mul_le_mul_of_nonneg_right hrem
    (show 0 ≤ (1 - s) * s ^ 4 by exact mul_nonneg (sub_nonneg.mpr hs.2) (by positivity))
  linarith only [h₂, h₄]

private theorem weighted_exp_integral_lower {y u : ℝ} (hy₀ : -1 ≤ y) (hy₂ : y ≤ 2)
    (hu : 0 ≤ u) (hu₂ : u ≤ 1 / 2) :
    y ^ 3 / 6 - 5 * y ^ 4 / 108 + u ^ 2 * y ^ 5 / 40 ≤
      y ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * (y * s) ^ (1 : ℕ) * Real.exp (-u * (y * s)) := by
  let a (s : ℝ) := y ^ 3 * ((1 - s) * s ^ (1 : ℕ))
  let b (s : ℝ) := (y ^ 4 / 2) * ((1 - s) * s ^ 2)
  let c (s : ℝ) := (u ^ 2 * y ^ 5 / 2) * ((1 - s) * s ^ 3)
  let d (s : ℝ) := (5 * y ^ 4 / 36) * ((1 - s) * s ^ 4)
  have ha : IntervalIntegrable a volume 0 1 :=
    (show Continuous a by unfold a; fun_prop).intervalIntegrable ..
  have hb : IntervalIntegrable b volume 0 1 :=
    (show Continuous b by unfold b; fun_prop).intervalIntegrable ..
  have hc : IntervalIntegrable c volume 0 1 :=
    (show Continuous c by unfold c; fun_prop).intervalIntegrable ..
  have hd : IntervalIntegrable d volume 0 1 :=
    (show Continuous d by unfold d; fun_prop).intervalIntegrable ..
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun s ↦ a s - b s + c s - d s)
    (g := fun s ↦ y ^ 2 * ((1 - s) * (y * s) ^ (1 : ℕ) * Real.exp (-u * (y * s))))
    zero_le_one (((ha.sub hb).add hc).sub hd) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (fun s hs ↦ by
      simpa only [a, b, c, d, pow_one] using weighted_exp_lower hy₀ hy₂ hu hu₂ hs)
  rw [intervalIntegral.integral_sub ((ha.sub hb).add hc) hd,
    intervalIntegral.integral_add (ha.sub hb) hc, intervalIntegral.integral_sub ha hb] at h
  simp only [a, b, c, d, intervalIntegral.integral_const_mul, unit_weight_moment] at h
  norm_num at h
  simp only [pow_one, neg_mul]
  linarith only [h]

private abbrev momentSum (p k : ℕ) : ℝ := ((gaps p).map fun g ↦ centered p g ^ k).sum

private theorem sum_map_le (l : List Gap) (f g : Gap → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    exact add_le_add (h x (List.mem_cons_self ..)) (ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

private theorem marginal_moment_sums {p : ℕ} (hp : 0 < p) :
    let h : ℝ := 3 / (p : ℝ)
    let C : ℝ := ((gaps p).length : ℝ) * (compositionMarginalVariance p / 2)
    momentSum p 3 = C * (2 * (2 + h) / 5) ∧
    momentSum p 4 = C * (2 * (6 + 6 * h - h ^ 2) / 5) ∧
    momentSum p 5 = C * (2 * (2 + h) * (4 + 4 * h - h ^ 2) / 7) := by
  dsimp only
  let h : ℝ := 3 / (p : ℝ)
  let C : ℝ := ((gaps p).length : ℝ) * (compositionMarginalVariance p / 2)
  have hC : 0 < C := mul_pos
    (by exact_mod_cast (word_counts_all p).2.1) (half_pos (compositionMarginalVariance_pos p))
  have e3 : normalizedMomentCoeffs 0 3 = [2/15, 1/15, 0, 0] := by
    have hn : certifiedMomentNumerators 0 3 = [96, 48, 0, 0] := by decide_cbv
    rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, hn]
    norm_num [certifiedMomentDenominator, Nat.factorial]
  have e4 : normalizedMomentCoeffs 0 4 = [1/10, 1/10, -1/60, 0, 0] := by
    have hn : certifiedMomentNumerators 0 4 = [1728, 1728, -288, 0, 0] := by decide_cbv
    rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, hn]
    norm_num [certifiedMomentDenominator, Nat.factorial]
  have e5 : normalizedMomentCoeffs 0 5 = [2/105, 1/35, 1/210, -1/420, 0, 0] := by
    have hn : certifiedMomentNumerators 0 5 = [11520, 17280, 2880, -1440, 0, 0] := by decide_cbv
    rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, hn]
    norm_num [certifiedMomentDenominator, Nat.factorial]
  have eval (k : ℕ) : momentHorner h (normalizedMomentCoeffs 0 (k + 2)) *
      (C * ((k + 2).factorial : ℝ)) = momentSum p (k + 2) :=
    (eq_div_iff (mul_pos hC (by positivity)).ne').mp (normalized_moment_eval_marginal hp k)
  have m3 := eval 1
  have m4 := eval 2
  have m5 := eval 3
  rw [e3] at m3
  rw [e4] at m4
  rw [e5] at m5
  norm_num [momentHorner, Nat.factorial] at m3 m4 m5
  change momentSum p 3 = C * (2 * (2 + h) / 5) ∧
    momentSum p 4 = C * (2 * (6 + 6 * h - h ^ 2) / 5) ∧
    momentSum p 5 = C * (2 * (2 + h) * (4 + 4 * h - h ^ 2) / 7)
  exact ⟨by linear_combination -m3, by linear_combination -m4, by linear_combination -m5⟩

/-- The regularized negative marginal decreases on the short left side of the separated strip. -/
theorem leftStrip_GPrime_nonneg {p : ℕ} (hp : 11 ≤ p) {u : ℝ}
    (hu : 0 < u) (hu₂ : u ≤ 1 / 2) :
    0 ≤ GPrime p 1 (-u) := by
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  let h : ℝ := 3 / (p : ℝ)
  have hh₀ : 0 ≤ h := by dsimp only [h]; positivity
  have hh₁ : h ≤ 3 / 11 := by
    dsimp only [h]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  let C : ℝ := ((gaps p).length : ℝ) * (compositionMarginalVariance p / 2)
  have hN : 0 < ((gaps p).length : ℝ) := by exact_mod_cast (word_counts_all p).2.1
  have hC : 0 < C := mul_pos hN (half_pos (compositionMarginalVariance_pos p))
  obtain ⟨m3, m4, m5⟩ := marginal_moment_sums hp₀
  change momentSum p 3 = C * (2 * (2 + h) / 5) at m3
  change momentSum p 4 = C * (2 * (6 + 6 * h - h ^ 2) / 5) at m4
  change momentSum p 5 = C * (2 * (2 + h) * (4 + 4 * h - h ^ 2) / 7) at m5
  have hC_lower : ((gaps p).length : ℝ) / 4 ≤ C := by
    dsimp only [C]
    rw [joint_normalization_eq hp₀]
    calc
      _ = ((gaps p).length : ℝ) * (1 / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by change 1 / 4 ≤ (1 + h) / 4; linarith) hN.le
  have hm3 : ((gaps p).length : ℝ) / 5 ≤ momentSum p 3 := by
    rw [m3]
    calc
      _ = (((gaps p).length : ℝ) / 4) * (4 / 5) := by ring
      _ ≤ C * (4 / 5) := mul_le_mul_of_nonneg_right hC_lower (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC.le
  have hm4 : momentSum p 4 ≤ (7 / 2) * momentSum p 3 := by
    rw [m3, m4]
    calc
      _ ≤ C * ((7 / 2) * (2 * (2 + h) / 5)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg h]) hC.le
      _ = _ := by ring
  have hm5 : 0 ≤ momentSum p 5 := by
    rw [m5]
    have hpoly : 0 ≤ 4 + 4 * h - h ^ 2 := by
      nlinarith [mul_nonneg hh₀ (show 0 ≤ 1 - h by linarith)]
    positivity
  let f (g : Gap) := centered p g ^ 2 * ∫ s in (0 : ℝ)..1,
    (1 - s) * (centered p g * s) ^ (1 : ℕ) * Real.exp (-u * (centered p g * s))
  let lower (g : Gap) := centered p g ^ 3 / 6 - 5 * centered p g ^ 4 / 108 +
    u ^ 2 * centered p g ^ 5 / 40
  have hbound := sum_map_le (gaps p) lower f fun g hg ↦
    weighted_exp_integral_lower (centered_bounds hp₀ hg).1 (centered_bounds hp₀ hg).2
      hu.le hu₂
  have hlower (l : List Gap) : (l.map lower).sum =
      (l.map fun g ↦ centered p g ^ 3).sum / 6 -
        5 * (l.map fun g ↦ centered p g ^ 4).sum / 108 +
        u ^ 2 * (l.map fun g ↦ centered p g ^ 5).sum / 40 := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, ih, lower]
      ring
  rw [hlower] at hbound
  change momentSum p 3 / 6 - 5 * momentSum p 4 / 108 + u ^ 2 * momentSum p 5 / 40 ≤
    ((gaps p).map f).sum at hbound
  rw [← (hasDerivAt_G p one_ne_zero (neg_ne_zero.mpr hu.ne')).deriv, ← iteratedDeriv_one,
    iteratedDeriv_G_eq_integral hp₀ one_ne_zero (neg_ne_zero.mpr hu.ne')]
  change 0 ≤ ((gaps p).map f).sum / (((gaps p).length : ℝ) * 1)
  apply (show (0 : ℝ) ≤ 1 / 1080 by norm_num).trans
  rw [mul_one, le_div_iff₀ hN]
  nlinarith only [hbound, hm3, hm4, mul_nonneg (sq_nonneg u) hm5]

#print axioms leftStrip_GPrime_nonneg

private theorem tilted_slope_le {v x : ℝ} (hv : 2 ≤ v) (hx : x ≤ 1) :
    x * Real.exp (v * x) ≤ 2 * Real.exp (v * x) - 2 - (2 * v - 1) * x := by
  let f (t : ℝ) := (2 - t) * Real.exp (v * t)
  let f' (t : ℝ) := ((2 - t) * v - 1) * Real.exp (v * t)
  have hexp (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Real.exp (v * s))
      (v * Real.exp (v * t)) t := by
    simpa only [mul_one, mul_comm] using ((hasDerivAt_id' t).const_mul v).exp
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    refine (((hasDerivAt_id' t).const_sub 2).mul (hexp t)).congr_deriv ?_
    dsimp only [f']
    ring
  have hf' (t : ℝ) : HasDerivAt f'
      (v * ((2 - t) * v - 2) * Real.exp (v * t)) t := by
    refine (((((hasDerivAt_id' t).const_sub 2).mul_const v).sub_const 1).mul
      (hexp t)).congr_deriv ?_
    ring
  have hderiv : deriv f = f' := funext fun t ↦ (hf t).deriv
  have hconv : ConvexOn ℝ (Iic 1) f := by
    apply convexOn_of_deriv2_nonneg' (convex_Iic _)
    · exact fun t _ ↦ (hf t).differentiableAt.differentiableWithinAt
    · rw [hderiv]
      exact fun t _ ↦ (hf' t).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (deriv f) t
      rw [hderiv, (hf' t).deriv]
      have hfactor : 0 ≤ (2 - t) * v - 2 := by
        have htv := mul_le_mul_of_nonneg_right (show 1 ≤ 2 - t by linarith [mem_Iic.mp ht])
          (show 0 ≤ v by linarith)
        linarith
      exact mul_nonneg (mul_nonneg (by linarith) hfactor) (Real.exp_pos _).le
  have h0 : (0 : ℝ) ∈ Iic 1 := by norm_num
  have hz : HasDerivAt f (2 * v - 1) 0 := by simpa [f'] using hf 0
  have hf0 : f 0 = 2 := by simp [f]
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · have hs := hconv.slope_le_of_hasDerivAt (mem_Iic.mpr hx) h0 hxneg hz
    rw [slope_def_field, hf0, div_le_iff₀ (sub_pos.mpr hxneg)] at hs
    dsimp only [f] at hs
    linarith
  · simp
  · have hs := hconv.le_slope_of_hasDerivAt h0 (mem_Iic.mpr hx) hxpos hz
    rw [slope_def_field, hf0, le_div_iff₀ (sub_pos.mpr hxpos)] at hs
    dsimp only [f] at hs
    linarith

private theorem negativeMarginal_logDeriv_of_exponent_bound {p : ℕ} (hp : 0 < p)
    {v K m : ℝ} (hv : 0 < v)
    (hpointwise : ∀ x : ℝ, x ≤ 1 →
      x * Real.exp (x * v) ≤ K * (Real.exp (x * v) - 1) + m * x) :
    deriv (fun t ↦ compositionMoment p 0 (-t)) v / compositionMoment p 0 (-v) ≤ K := by
  let x (g : Gap) : ℝ := -centered p g
  let e (g : Gap) (t : ℝ) : ℝ := Real.exp (x g * t)
  let d (g : Gap) : ℝ := x g * e g v
  let N : ℝ := (gaps p).length
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (word_counts_all p).2.1
  have hsum (l : List Gap) :
      HasDerivAt (fun t ↦ (l.map fun g ↦ e g t).sum) (l.map d).sum v := by
    induction l with
    | nil => simpa using hasDerivAt_const v (0 : ℝ)
    | cons g l ih =>
      have h : HasDerivAt (e g) (d g) v := by
        simpa only [e, d, mul_one, mul_comm, one_mul] using
          ((hasDerivAt_id' v).const_mul (x g)).exp
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using h.add ih
  have heq (t : ℝ) :
      ((gaps p).map fun g ↦ e g t).sum / N - 1 = compositionMoment p 0 (-t) := by
    simp only [compositionMoment, e, x, mul_zero, zero_add, mul_neg, neg_mul, N]
    rfl
  have hm := (((hsum (gaps p)).div_const N).sub_const 1).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ (heq t).symm)
  let b (g : Gap) := K * (e g v - 1) + m * x g
  have hpoint (g : Gap) (hg : g ∈ gaps p) : d g ≤ b g := by
    have hx : x g ≤ 1 := by dsimp only [x]; linarith [(centered_bounds hp hg).1]
    exact hpointwise (x g) hx
  have hbound := sum_map_le (gaps p) d b hpoint
  have hb (l : List Gap) : (l.map b).sum =
      K * (l.map fun g ↦ e g v).sum - K * l.length + m * (l.map x).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih, b]
      ring
  have hxsum : ((gaps p).map x).sum = 0 := by
    calc
      _ = ((gaps p).map fun g ↦ (-1 : ℝ) * centered p g).sum := by simp only [x, neg_one_mul]
      _ = 0 := by
        rw [List.sum_map_mul_left]
        change (-1 : ℝ) * ((gaps p).map (centered p)).sum = 0
        rw [show ((gaps p).map (centered p)).sum = 0 from composition_last_exponent_sum_zero hp,
          mul_zero]
  have hmpos := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  rw [hm.deriv]
  apply (div_le_iff₀ hmpos).2
  rw [div_le_iff₀ hN, ← heq]
  rw [hb, hxsum, mul_zero, add_zero] at hbound
  calc
    _ ≤ K * ((gaps p).map fun g ↦ e g v).sum - K * N := hbound
    _ = _ := by
      rw [mul_assoc, sub_mul, div_mul_cancel₀ _ hN.ne', one_mul]
      ring

/-- The negative marginal has logarithmic slope at most two in the separated strip. -/
theorem negativeMarginal_logDeriv_le {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 2 ≤ v) :
    deriv (fun t ↦ compositionMoment p 0 (-t)) v / compositionMoment p 0 (-v) ≤ 2 := by
  refine negativeMarginal_logDeriv_of_exponent_bound hp (by linarith) (m := 1 - 2 * v) ?_
  intro x hx
  rw [mul_comm x v]
  nlinarith only [tilted_slope_le hv hx]

/-- The tilted negative marginal has logarithmic slope at most
the quadratic slope plus the largest reflected exponent. -/
theorem negativeMarginal_logDeriv_le_two_div_add_one {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : 0 < t) :
    deriv (fun s ↦ compositionMoment p 0 (-s)) t / compositionMoment p 0 (-t) ≤
      2 / t + 1 := by
  let q := G p 1
  let y (g : Gap) := centered p g
  let weight (g : Gap) (s : ℝ) := (1 - s) * Real.exp ((-t) * (y g * s))
  let value (g : Gap) := y g ^ 2 * ∫ s in (0 : ℝ)..1, weight g s
  let slope (g : Gap) := y g ^ 2 * ∫ s in (0 : ℝ)..1, weight g s * (y g * s)
  have hpoint (g : Gap) (hg : g ∈ gaps p) : -slope g ≤ value g := by
    have hleft : Continuous (fun s ↦ -(weight g s * (y g * s))) := by
      unfold weight
      fun_prop
    have hright : Continuous (weight g) := by unfold weight; fun_prop
    have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
      (fun s hs ↦ by
        have hy : -1 ≤ y g := (centered_bounds hp hg).1
        have hys : -(y g * s) ≤ 1 := by
          calc
            -(y g * s) = (-y g) * s := (neg_mul _ _).symm
            _ ≤ 1 * s := mul_le_mul_of_nonneg_right (by linarith) hs.1
            _ ≤ 1 := by simpa using hs.2
        have hw : 0 ≤ weight g s :=
          mul_nonneg (sub_nonneg.mpr hs.2) (Real.exp_pos _).le
        simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hys hw)
    rw [intervalIntegral.integral_neg] at h
    simpa only [slope, value, mul_neg] using
      mul_le_mul_of_nonneg_left h (sq_nonneg (y g))
  have hsum := sum_map_le (gaps p) (fun g ↦ (-1 : ℝ) * slope g) value
    (fun g hg ↦ by simpa only [neg_one_mul] using hpoint g hg)
  rw [List.sum_map_mul_left, neg_one_mul] at hsum
  have hslope : -deriv q (-t) ≤ q (-t) := by
    have h0 := iteratedDeriv_G_eq_integral (p := p) hp (c := 1) (by norm_num)
      (neg_ne_zero.mpr ht.ne') 0
    have h1 := iteratedDeriv_G_eq_integral (p := p) hp (c := 1) (by norm_num)
      (neg_ne_zero.mpr ht.ne') 1
    rw [iteratedDeriv_zero] at h0
    rw [iteratedDeriv_one] at h1
    change -deriv (G p 1) (-t) ≤ G p 1 (-t)
    rw [h0, h1]
    unfold integralMarginalDerivative
    simp only [pow_zero, pow_one, mul_one]
    rw [← neg_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [slope, value, weight, y, centered, mul_right_comm] using hsum
  have hG' : HasDerivAt (fun s : ℝ ↦ q (-s)) (-deriv q (-t)) t := by
    have h := (hasDerivAt_G p (c := 1) (by norm_num) (neg_ne_zero.mpr ht.ne'))
    simpa only [q, h.deriv, Function.comp_def, id_eq, mul_neg, mul_one] using
      (h.comp t (hasDerivAt_id' t).neg)
  have hProd : HasDerivAt (fun s : ℝ ↦ s ^ 2 * q (-s))
      (2 * t * q (-t) + t ^ 2 * (-deriv q (-t))) t := by
    simpa using (hasDerivAt_pow 2 t).fun_mul hG'
  have hEq (s : ℝ) (hs : 0 < s) :
      s ^ 2 * q (-s) = compositionMoment p 0 (-s) := by
    simp only [q, G, one_mul, neg_sq]
    exact mul_div_cancel₀ _ (pow_ne_zero _ hs.ne')
  have hDeriv := hProd.congr_of_eventuallyEq (by
    filter_upwards [eventually_gt_nhds ht] with s hs using (hEq s hs).symm)
  rw [hDeriv.deriv]
  apply (div_le_iff₀ (compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne'))).2
  rw [← hEq t ht]
  calc
    _ ≤ 2 * t * q (-t) + t ^ 2 * q (-t) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hslope (sq_nonneg t)) _
    _ = _ := by field_simp [ht.ne'] <;> ring

private theorem exp_gap_two_sub_antitone :
    Antitone (fun t : ℝ ↦ (2 - t) * Real.exp t - 2 - t) := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ ↦ (2 - x) * Real.exp x - 2 - x)
      ((1 - t) * Real.exp t - 1) t := by
    have h := (((hasDerivAt_id' t).const_sub 2).fun_mul
      (Real.hasDerivAt_exp t)).sub_const 2 |>.sub (hasDerivAt_id' t)
    convert h using 1 <;> ring
  apply antitone_of_deriv_nonpos (fun t ↦ (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith only [h]

private theorem tilted_gap_slope_le {u x : ℝ} (hu : 0 < u) (hx : x ≤ 1) :
    x * (Real.exp (x * u) - 1) ≤ (Real.exp u - 1) / (Real.exp u - 1 - u) *
      (Real.exp (x * u) - 1 - x * u) := by
  let E (t : ℝ) := Real.exp t - 1
  let P (t : ℝ) := E t - t
  let F (t : ℝ) := t * E t / P t
  have hP {t : ℝ} (ht : t ≠ 0) : 0 < P t := by
    dsimp only [P, E]
    linarith only [Real.add_one_lt_exp ht]
  have hderiv {t : ℝ} (ht : 0 < t) :
      HasDerivAt F ((E t ^ 2 - t ^ 2 * Real.exp t) / P t ^ 2) t := by
    have he : HasDerivAt E (Real.exp t) t := (Real.hasDerivAt_exp t).sub_const 1
    have hp : HasDerivAt P (Real.exp t - 1) t := he.sub (hasDerivAt_id' t)
    apply (((hasDerivAt_id' t).fun_mul he).div hp (hP ht.ne').ne').congr_deriv
    dsimp only [P, E]
    congr 1
    ring
  have hmono : MonotoneOn F (Ioi 0) := by
    have hl {t : ℝ} (ht : t ∈ Ioi 0) := (hderiv ht).differentiableAt
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0) (fun t ht ↦
      (hl ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hl (interior_subset ht)).differentiableWithinAt
    · intro t ht
      have ht₀ : 0 < t := interior_subset ht
      rw [(hderiv ht₀).deriv]
      apply div_nonneg _ (sq_nonneg _)
      let e := Real.exp (t / 2)
      let s := 2 * Real.sinh (t / 2)
      have hs : t ≤ s := by
        dsimp only [s]
        linarith only [Real.self_le_sinh_iff.mpr (by positivity : 0 ≤ t / 2)]
      have he : Real.exp t = e ^ 2 := by dsimp only [e]; rw [pow_two, ← Real.exp_add]; ring_nf
      have hE : E t = e * s := by
        dsimp only [E, s]
        rw [he]
        dsimp only [e]
        rw [Real.sinh_eq, Real.exp_neg]
        field_simp [(Real.exp_pos (t / 2)).ne'] <;> ring
      rw [hE, he, mul_pow]
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀.le hs 2) (sq_nonneg e)
      nlinarith only [h]
  let z := x * u
  change x * E z ≤ E u / P u * P z
  by_cases hz : z = 0
  · simp [hz, E, P]
  have hF : F z ≤ F u := by
    by_cases hz' : 0 < z
    · exact hmono hz' hu (by dsimp only [z]; simpa using mul_le_mul_of_nonneg_right hx hu.le)
    · have hleft := exp_gap_two_sub_antitone (le_of_not_gt hz')
      have hright := exp_gap_two_sub_antitone hu.le
      have hl : F z ≤ 2 := by
        apply (div_le_iff₀ (hP hz)).2
        simp only [Real.exp_zero] at hleft
        dsimp only [P, E]
        nlinarith only [hleft]
      have hr : 2 ≤ F u := by
        apply (le_div_iff₀ (hP hu.ne')).2
        simp only [Real.exp_zero] at hright
        dsimp only [P, E]
        nlinarith only [hright]
      exact hl.trans hr
  have hmul := mul_le_mul_of_nonneg_right hF (hP hz).le
  dsimp only [F] at hmul
  rw [div_mul_cancel₀ _ (hP hz).ne'] at hmul
  apply (mul_le_mul_iff_right₀ hu).mp
  convert hmul using 1 <;> dsimp only [z] <;> ring

private theorem exp_gap_quadratic_nonneg {u : ℝ} (hu : 0 < u) (hfour : u ≤ 4) :
    0 ≤ (Real.exp u - 1) ^ 2 + (100 - 26 * u) * (Real.exp u - 1) - 100 * u := by
  let x := Real.exp u - 1
  let q := u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120
  have hsum := Real.sum_le_exp_of_nonneg hu.le 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  have hqx : q ≤ x := by dsimp only [q, x]; linarith only [hsum]
  have huq : u ≤ q := by
    dsimp only [q]
    have h : 0 ≤ u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 := by positivity
    linarith only [h]
  have hmono := mul_nonneg (sub_nonneg.mpr hqx)
    (show 0 ≤ x + q + (100 - 26 * u) by linarith [huq.trans hqx])
  have h3 : u ^ 3 ≤ 4 * u ^ 2 := by
    convert mul_le_mul_of_nonneg_left hfour (sq_nonneg u) using 1 <;> ring
  have h6 : u ^ 6 ≤ 64 * u ^ 3 := by
    have hpow : u ^ 3 ≤ (4 : ℝ) ^ 3 := pow_le_pow_left₀ hu.le hfour 3
    convert mul_le_mul_of_nonneg_left hpow (pow_nonneg hu.le 3) using 1 <;> ring
  have hremainder : 0 ≤ u ^ 7 / 45 + 13 * u ^ 8 / 2880 + u ^ 9 / 1440 + u ^ 10 / 14400 := by
    positivity
  have hpoly : q ^ 2 + (100 - 26 * u) * q - 100 * u =
      25 * u ^ 2 + 14 * u ^ 3 / 3 + 5 * u ^ 4 / 12 - 47 * u ^ 6 / 360 +
      (u ^ 7 / 45 + 13 * u ^ 8 / 2880 + u ^ 9 / 1440 + u ^ 10 / 14400) := by
    dsimp only [q]
    ring
  change 0 ≤ x ^ 2 + (100 - 26 * u) * x - 100 * u
  nlinarith only [hpoly, hmono, h3, h6, hremainder, sq_nonneg u, pow_nonneg hu.le 4]

private theorem exp_gap_ratio_le {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1) :
    (Real.exp u - 1) / (Real.exp u - 1 - u) ≤ 2 / u + 1 / 2 := by
  let x := Real.exp u - 1
  have hsum := Real.sum_le_exp_of_nonneg hu.le 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  have hx : u + u ^ 2 / 2 + u ^ 3 / 6 ≤ x := by dsimp only [x]; linarith only [hsum]
  have hx' : 0 < x - u := by
    have h := sq_pos_of_pos hu
    have h3 := pow_nonneg hu.le 3
    nlinarith only [hx, h, h3]
  have hp := mul_le_mul_of_nonneg_left hx (show 0 ≤ 4 - u by linarith)
  have hq := mul_nonneg (pow_nonneg hu.le 3) (sub_nonneg.mpr hsmall)
  change x / (x-u) ≤ 2 / u + 1 / 2
  rw [div_le_iff₀ hx']
  apply (mul_le_mul_iff_left₀ hu).mp
  field_simp [hu.ne']
  nlinarith only [hp, hq]

/-- The centered negative marginal controls the lower-coordinate log slope
uniformly up to four, including the stronger margin for small coordinates. -/
theorem separatedGap_lowerSlope_bounds {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u)
    (hfour : u ≤ 4) :
    let b := 1 + 2 / (Real.exp u - 1) -
      (deriv (fun t ↦ compositionMoment p 0 (-t)) u / compositionMoment p 0 (-u)) / 2
    12 / 25 ≤ b ∧ (u ≤ 1 → 3 / 4 ≤ b) := by
  let E := Real.exp u - 1
  let K := E / (E - u)
  have hE : 0 < E := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hP : 0 < E - u := by dsimp only [E]; linarith [Real.add_one_lt_exp hu.ne']
  have hK : deriv (fun t ↦ compositionMoment p 0 (-t)) u /
      compositionMoment p 0 (-u) ≤ K := by
    refine negativeMarginal_logDeriv_of_exponent_bound hp hu (m := 1 - K * u) ?_
    intro x hx
    have h := tilted_gap_slope_le hu hx
    change x * (Real.exp (x * u) - 1) ≤ K * (Real.exp (x * u) - 1 - x * u) at h
    nlinarith only [h]
  have hbase : (12 : ℝ) / 25 ≤ 1 + 2 / E - K / 2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hE hP)).mp
    dsimp only [K]
    field_simp [hE.ne', hP.ne']
    have h := exp_gap_quadratic_nonneg hu hfour
    change 0 ≤ E ^ 2 + (100 - 26 * u) * E - 100 * u at h
    nlinarith only [h]
  dsimp only
  change 12 / 25 ≤ 1 + 2 / E - _ / 2 ∧ (u ≤ 1 → 3 / 4 ≤ 1 + 2 / E - _ / 2)
  constructor
  · linarith only [hbase, hK]
  · intro hsmall
    have hk := exp_gap_ratio_le hu hsmall
    change K ≤ 2 / u + 1 / 2 at hk
    have hquot : 2 / u ≤ 1 + 2 / E := by
      apply (mul_le_mul_iff_left₀ (mul_pos hu hE)).mp
      field_simp [hu.ne', hE.ne']
      have h := exp_gap_two_sub_antitone hu.le
      norm_num [Real.exp_zero] at h
      rw [show Real.exp u = E + 1 by dsimp only [E]; ring] at h
      nlinarith only [h]
    have hinv : 1 ≤ 1 / u := by apply (le_div_iff₀ hu).2; simpa using hsmall
    rw [show 2 / u = 2 * (1 / u) by ring] at hk hquot
    linarith only [hK, hk, hquot, hinv]

#print axioms negativeMarginal_logDeriv_le
#print axioms separatedGap_lowerSlope_bounds

end RefinedBMV.PositiveCenter
