/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/HalfGapSlope
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform reflected marginal slope bound from the half-gap endpoint. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.WeightedTaylorReplay

/-! # The reflected marginal slope above a half gap -/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace RefinedBMV.PositiveCenter

open SmallCorner

noncomputable section

private abbrev varianceHalf (p : ℕ) : ℝ := compositionMarginalVariance p / 2

private abbrev marginal (p : ℕ) : ℕ → ℝ → ℝ :=
  integralMarginalDerivative p (varianceHalf p)

private theorem hasDerivAt_marginal (p k : ℕ) (t : ℝ) :
    HasDerivAt (marginal p k) (marginal p (k + 1) t) t := by
  simpa [affineMarginalJet] using (continuedMarginalJet_isAt p k 0 1 0 t).2.1

private theorem marginal_second_nonneg (p : ℕ) (t : ℝ) : 0 ≤ marginal p 2 t := by
  unfold marginal integralMarginalDerivative
  have hc := half_pos (compositionMarginalVariance_pos p)
  apply div_nonneg _ (mul_nonneg (Nat.cast_nonneg _) hc.le)
  apply List.sum_nonneg
  intro w hw
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hw
  apply mul_nonneg (sq_nonneg _)
  exact intervalIntegral.integral_nonneg zero_le_one fun s hs ↦
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _)) (Real.exp_pos _).le

private def addCoeffs : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addCoeffs xs ys

private theorem momentHorner_addCoeffs (h : ℝ) (xs ys : List ℚ) :
    momentHorner h (addCoeffs xs ys) = momentHorner h xs + momentHorner h ys := by
  induction xs generalizing ys with
  | nil => simp [addCoeffs, momentHorner]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoeffs, momentHorner]
    | cons y ys => simp only [addCoeffs, momentHorner, Rat.cast_add, ih]; ring

private theorem momentHorner_scale (h : ℝ) (a : ℚ) (cs : List ℚ) :
    momentHorner h (cs.map (a * ·)) = a * momentHorner h cs := by
  induction cs with
  | nil => simp [momentHorner]
  | cons c cs ih => simp only [List.map_cons, momentHorner, Rat.cast_mul, ih]; ring

/-- Sum the Taylor terms as rational coefficient lists in the degree parameter. -/
private def endpointCoeffs : ℕ → List ℚ
  | 0 => []
  | i + 1 => addCoeffs (endpointCoeffs i)
      ((certifiedMomentCoeffs 0 (i + 3)).map (((i + 1 : ℕ) : ℚ) * (-2 / 3) ^ i * ·))

private abbrev endpointTerm (h : ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * (-2 / 3) ^ i * momentHorner h (normalizedMomentCoeffs 0 (i + 3))

private theorem endpointCoeffs_eval (h : ℝ) (n : ℕ) :
    momentHorner h (endpointCoeffs n) = ∑ i ∈ Finset.range n, endpointTerm h i := by
  induction n with
  | zero => simp [endpointCoeffs, momentHorner]
  | succ n ih =>
    rw [endpointCoeffs, momentHorner_addCoeffs, ih, Finset.sum_range_succ,
      momentHorner_scale, certifiedMomentCoeffs_eq]
    norm_num only [endpointTerm, Rat.cast_mul, Rat.cast_natCast, Nat.cast_add, Nat.cast_one,
      Rat.cast_add, Rat.cast_one, Rat.cast_pow, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]

private theorem marginalTaylor_endpoint_eq {p : ℕ} (hp : 0 < p) :
    marginalTaylorPolynomial p 1 (-2 / 3) =
      ∑ i ∈ Finset.range 22, endpointTerm (3 / (p : ℝ)) i := by
  rw [marginalTaylorPolynomial]
  apply Finset.sum_congr rfl
  intro i _
  unfold endpointTerm
  let x (j : ℕ) : ℝ := 3 * (j : ℝ) / (p : ℝ) - 1
  let C : ℝ := ((DimThree.gaps p).length : ℝ) * varianceHalf p
  have hcycle := ((DimThree.gaps_cycle_all p).map fun g ↦ x g.2.1 ^ (i + 3)).sum_eq
  simp only [List.map_map, Function.comp_def] at hcycle
  rw [show i + 3 = (1 + i) + 2 by omega, normalized_moment_eval_marginal hp]
  change ((DimThree.gaps p).map fun g ↦ x g.2.1 ^ 2 *
      (x g.2.1 ^ (1 + i) * x g.2.2 ^ 0)).sum / C * (-2 / 3) ^ i /
        ((i.factorial : ℝ) * (((1 + i : ℕ) : ℝ) + 1) * (((1 + i : ℕ) : ℝ) + 2)) =
    ((i : ℝ) + 1) * (-2 / 3) ^ i *
      (((DimThree.gaps p).map fun g ↦ x g.2.2 ^ ((1 + i) + 2)).sum /
        (C * (((1 + i) + 2).factorial : ℝ)))
  simp only [pow_zero, mul_one, ← pow_add, show 1 + i = i + 1 by omega, hcycle,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  field_simp [hi.ne']; ring_nf

private abbrev rationalHorner (h : ℚ) : List ℚ → ℚ := marginalHorner (· + ·) (· * ·) 0 h

private theorem abs_momentHorner_le {h : ℝ} {H : ℚ} (hh : 0 ≤ h) (hle : h ≤ H)
    (cs : List ℚ) : |momentHorner h cs| ≤ (rationalHorner H (cs.map abs) : ℝ) := by
  induction cs with
  | nil => simp [momentHorner, marginalHorner]
  | cons c cs ih =>
    simp only [momentHorner, List.map_cons, rationalHorner, marginalHorner,
      Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
    calc
      _ ≤ |(c : ℝ)| + |h * momentHorner h cs| := abs_add_le _ _
      _ ≤ |(c : ℝ)| + (H : ℝ) * (rationalHorner H (cs.map abs) : ℝ) := by
        rw [abs_mul, abs_of_nonneg hh]
        exact add_le_add le_rfl (mul_le_mul hle ih (abs_nonneg _) (hh.trans hle))
      _ = (rationalHorner H (cs.map abs) : ℝ) * H + |(c : ℝ)| := by ring

private def endpointLower (cs : List ℚ) : ℚ :=
  cs.headD 0 - (3 / 11) * rationalHorner (3 / 11) (cs.tail.map abs)

private theorem endpointLower_le {h : ℝ} (hh : 0 ≤ h) (hle : h ≤ (3 / 11 : ℝ))
    (cs : List ℚ) : (endpointLower cs : ℝ) ≤ momentHorner h cs := by
  cases cs with
  | nil => norm_num [endpointLower, momentHorner, marginalHorner]
  | cons c cs =>
    have hB : h ≤ ((3 / 11 : ℚ) : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hle
    have hb := mul_le_mul hB (abs_momentHorner_le hh hB cs) (abs_nonneg _) (hh.trans hB)
    have ha := mul_le_mul_of_nonneg_left (neg_le_abs (momentHorner h cs)) hh
    simp only [endpointLower, List.headD, List.tail_cons, momentHorner, Rat.cast_sub, Rat.cast_mul]
    linarith only [hb, ha]

set_option maxHeartbeats 0 in
-- Compute the rational coefficient sum before bounding its nonconstant terms.
set_option cbv.maxSteps 1000000 in
private theorem endpointLower_certified :
    (1 / 200 : ℚ) + 1 / 2 ^ 30 + 1 / 50000 < endpointLower (endpointCoeffs 8) := by
  decide_cbv

/-- The moments beyond the first eight contribute at most `1/50000` in absolute value. -/
private theorem marginalTaylor_endpoint_lower {p : ℕ} (hp : 0 < p) :
    momentHorner (3 / (p : ℝ)) (endpointCoeffs 8) - 1 / 50000 ≤
      marginalTaylorPolynomial p 1 (-2 / 3) := by
  let h : ℝ := 3 / (p : ℝ)
  let bound (i : ℕ) : ℝ := ((i : ℝ) + 1) * (2 / 3) ^ i * (2 ^ (i + 2) / (i + 3).factorial)
  have hterm (i : ℕ) : -bound i ≤ endpointTerm h i := by
    have habs : |endpointTerm h i| ≤ bound i := by
      dsimp only [endpointTerm, bound]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (i : ℝ) + 1), abs_pow,
        show |(-2 / 3 : ℝ)| = 2 / 3 by norm_num]
      exact mul_le_mul_of_nonneg_left (normalized_moment_abs_bound_marginal hp (i + 1))
        (by positivity)
    exact (abs_le.mp habs).1
  have htail := Finset.sum_le_sum (s := Finset.range 14) (fun i _ ↦ hterm (8 + i))
  rw [Finset.sum_neg_distrib] at htail
  have hbound : (∑ i ∈ Finset.range 14, bound (8 + i)) ≤ 1 / 50000 := by
    norm_num [bound, Finset.sum_range_succ, Nat.factorial]
  rw [marginalTaylor_endpoint_eq hp, Finset.sum_range_add (endpointTerm h) 8 14,
    ← endpointCoeffs_eval]
  rw [sub_eq_add_neg]
  exact add_le_add le_rfl ((neg_le_neg hbound).trans htail)

private theorem marginal_first_endpoint_gt {p : ℕ} (hp : 11 ≤ p) :
    1 / 200 < marginal p 1 (-2 / 3) := by
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have ht : |(-2 / 3 : ℝ)| ≤ 1 := by norm_num
  have he := (abs_le.mp (integralMarginalDerivative_sub_taylor_le hp₀ (order := 1)
    (by decide) ht)).1
  have hl := endpointLower_le (h := 3 / (p : ℝ)) (by positivity)
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR) (endpointCoeffs 8)
  have hc : (1 / 200 : ℝ) + 1 / 2 ^ 30 + 1 / 50000 <
      (endpointLower (endpointCoeffs 8) : ℝ) := by
    let lower : ℚ := 1 / 200 + 1 / 2 ^ 30 + 1 / 50000
    have hc' : (lower : ℝ) < (endpointLower (endpointCoeffs 8) : ℝ) :=
      Rat.cast_lt.mpr endpointLower_certified
    simpa only [lower, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
      using hc'
  change -(1 / (2 : ℝ) ^ 30) ≤ marginal p 1 (-2 / 3) -
    marginalTaylorPolynomial p 1 (-2 / 3) at he
  linarith only [he, hl, hc, marginalTaylor_endpoint_lower hp₀]

private theorem marginal_first_neg_pos {p : ℕ} (hp : 11 ≤ p) {v : ℝ} (hv : v ≤ 2 / 3) :
    0 < marginal p 1 (-v) := by
  have hmono : Monotone (marginal p 1) :=
    monotone_of_deriv_nonneg (fun t ↦ (hasDerivAt_marginal p 1 t).differentiableAt) fun t ↦ by
      rw [(hasDerivAt_marginal p 1 t).deriv]
      exact marginal_second_nonneg p t
  exact ((by norm_num : (0 : ℝ) < 1 / 200).trans (marginal_first_endpoint_gt hp)).trans_le
    (hmono (by linarith))

private theorem marginal_zero_eq_G {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    marginal p 0 t = G p (varianceHalf p) t := by
  have hc := half_pos (compositionMarginalVariance_pos p)
  simpa only [iteratedDeriv_zero] using (iteratedDeriv_G_eq_integral hp hc.ne' ht 0).symm

private theorem marginal_zero_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    0 < marginal p 0 t := by
  rw [marginal_zero_eq_G hp ht]
  exact G_pos hp (half_pos (compositionMarginalVariance_pos p)) ht

private theorem reflectedHalfLogSlope_eq_marginal {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    reflectedHalfLogSlope (compositionMoment p 0) v =
      1 / v - marginal p 1 (-v) / (2 * marginal p 0 (-v)) := by
  have hc := half_pos (compositionMarginalVariance_pos p)
  have hfactor (x : ℝ) (hx : x ≠ 0) :
      compositionMoment p 0 (-x) = varianceHalf p * x ^ 2 * marginal p 0 (-x) := by
    rw [marginal_zero_eq_G hp (neg_ne_zero.mpr hx), G, neg_sq,
      mul_div_cancel₀ _ (mul_ne_zero hc.ne' (pow_ne_zero _ hx))]
  have hz := marginal_zero_pos hp (neg_ne_zero.mpr hv.ne')
  have hpow : HasDerivAt (fun x : ℝ ↦ varianceHalf p * x ^ 2) (varianceHalf p * (2 * v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_mul (varianceHalf p)
  have hZ := (hasDerivAt_marginal p 0 (-v)).comp v (hasDerivAt_id' v).neg
  have hnear : (fun x ↦ compositionMoment p 0 (-x)) =ᶠ[𝓝 v]
      (fun x ↦ varianceHalf p * x ^ 2 * marginal p 0 (-x)) := by
    filter_upwards [eventually_ne_nhds hv.ne'] with x hx using hfactor x hx
  have hd := (hpow.mul hZ).congr_of_eventuallyEq hnear
  rw [reflectedHalfLogSlope, hd.deriv, hfactor v hv.ne']
  dsimp only [id_eq, Function.comp_apply, zero_add]
  field_simp [(compositionMarginalVariance_pos p).ne', hv.ne', hz.ne']; ring

/-- The reflected half-log slope is below `2 + 3/p` throughout the half-gap range. -/
theorem reflectedHalfLogSlope_lt_two_add_spacing {p : ℕ} (hp : 11 ≤ p) {v : ℝ}
    (hv : 1 / 2 ≤ v) : reflectedHalfLogSlope (compositionMoment p 0) v < 2 + 3 / (p : ℝ) := by
  have hp₀ : 0 < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hh : 0 < 3 / (p : ℝ) := by positivity
  have hv₀ : 0 < v := by linarith
  by_cases htail : 2 / 3 ≤ v
  · have h := upperTail_marginal_logDeriv hp₀ hv₀
    have hi : 2 / v ≤ 3 := (div_le_iff₀ hv₀).mpr (by linarith)
    unfold reflectedHalfLogSlope
    linarith only [h, hi, hh]
  · have hz := marginal_zero_pos hp₀ (neg_ne_zero.mpr hv₀.ne')
    have hd := marginal_first_neg_pos hp (le_of_lt (lt_of_not_ge htail))
    have hs : 0 < marginal p 1 (-v) / (2 * marginal p 0 (-v)) :=
      div_pos hd (mul_pos (by norm_num) hz)
    have hi : 1 / v ≤ 2 := (div_le_iff₀ hv₀).mpr (by linarith)
    rw [reflectedHalfLogSlope_eq_marginal hp₀ hv₀]
    linarith only [hs, hi, hh]

/-- On the residual region, evaluating the four marginal moments gives a strict upper
bound for the normalized mixed derivative even at the half-gap cutoff. -/
theorem logKernel_mixed_lt_fourPoint_of_half {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : 1 / 2 ≤ v) :
    Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) *
      deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v <
      compactMixedT p u v (compositionMomentFourPoint p u v) - compactMixedQ p u v := by
  have hp₀ : 0 < p := by omega
  rw [logKernel_mixed_eq_compactMixed hp₀ hu huv]
  exact sub_lt_sub_right
    (compactMixedT_strictAnti_of_slope hp₀ hu (reflectedHalfLogSlope_lt_two_add_spacing hp hv)
      (show compositionMomentFourPoint p u v < 1 + compositionMoment p u v from
        compositionMoment_fourPoint_lower hp₀ hu v)) _

#print axioms reflectedHalfLogSlope_lt_two_add_spacing
#print axioms logKernel_mixed_lt_fourPoint_of_half

end

end RefinedBMV.PositiveCenter
