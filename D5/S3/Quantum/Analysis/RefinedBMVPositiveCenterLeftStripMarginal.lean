/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripMarginal
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative-marginal slopes for the separated positive-center strip. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial

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

/-- The negative marginal has logarithmic slope at most two in the separated strip. -/
theorem negativeMarginal_logDeriv_le {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 2 ≤ v) :
    deriv (fun t ↦ compositionMoment p 0 (-t)) v / compositionMoment p 0 (-v) ≤ 2 := by
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
  let b (g : Gap) := 2 * e g v - 2 - (2 * v - 1) * x g
  have hpoint (g : Gap) (hg : g ∈ gaps p) : d g ≤ b g := by
    have hx : x g ≤ 1 := by dsimp only [x]; linarith [(centered_bounds hp hg).1]
    simpa only [b, d, e, mul_comm (x g) v] using tilted_slope_le hv hx
  have hbound := sum_map_le (gaps p) d b hpoint
  have hb (l : List Gap) : (l.map b).sum =
      2 * (l.map fun g ↦ e g v).sum - 2 * l.length - (2 * v - 1) * (l.map x).sum := by
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
  have hvpos : 0 < v := by linarith
  have hmpos := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hvpos.ne')
  rw [hm.deriv]
  apply (div_le_iff₀ hmpos).2
  rw [div_le_iff₀ hN, ← heq]
  rw [hb, hxsum, mul_zero, sub_zero] at hbound
  calc
    _ ≤ 2 * ((gaps p).map fun g ↦ e g v).sum - 2 * N := hbound
    _ = _ := by
      rw [mul_assoc, sub_mul, div_mul_cancel₀ _ hN.ne', one_mul]
      ring

#print axioms negativeMarginal_logDeriv_le

end RefinedBMV.PositiveCenter
