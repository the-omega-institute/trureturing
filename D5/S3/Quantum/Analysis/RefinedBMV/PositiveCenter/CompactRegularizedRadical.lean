/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactRegularizedRadical
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Collision regularization of the normalized mixed radical. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor

/-! # Removing the collision singularity of the mixed radical -/

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open SmallCorner
open DimThree (gaps word_counts_all)

private theorem gap_count_pos (p : ℕ) : (0 : ℝ) < (gaps p).length := by
  exact_mod_cast (word_counts_all p).2.1

/-- The quadratic coefficient of the centered marginal, with spacing `3/p`. -/
def compactKappa (p : ℕ) : ℝ := (1 + 3 / (p : ℝ)) / 4

private theorem compactKappa_eq_varianceHalf {p : ℕ} (hp : 0 < p) :
    compactKappa p = compositionMarginalVariance p / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold compactKappa compositionMarginalVariance
  rw [(centered_marginal_sums hp).2]
  field_simp [(gap_count_pos p).ne', hpR]
  norm_num

private theorem compactKappa_pos {p : ℕ} (hp : 0 < p) : 0 < compactKappa p := by
  rw [compactKappa_eq_varianceHalf hp]
  exact half_pos (compositionMarginalVariance_pos p)

/-- The normalized marginal continued across zero by its integral formula. -/
def compactZ (p : ℕ) : ℝ → ℝ := integralMarginalDerivative p (compactKappa p) 0

theorem compactZ_eq_G {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    compactZ p t = G p (compactKappa p) t := by
  simpa only [compactZ, iteratedDeriv_zero] using
    (iteratedDeriv_G_eq_integral hp (compactKappa_pos hp).ne' ht 0).symm

@[simp] theorem compactZ_zero {p : ℕ} (hp : 0 < p) : compactZ p 0 = 1 := by
  have hhalf : (∫ s in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    simpa using unit_weight_moment 0
  unfold compactZ integralMarginalDerivative
  simp only [pow_zero, zero_mul, Real.exp_zero, mul_one, hhalf, List.sum_map_mul_right]
  rw [compactKappa_eq_varianceHalf hp]
  have hsum : ((gaps p).map fun g ↦ (3 * (g.2.2 : ℝ) / p - 1) ^ 2).sum =
      (gaps p).length * compositionMarginalVariance p := by
    unfold compositionMarginalVariance
    exact (mul_div_cancel₀ _ (gap_count_pos p).ne').symm
  rw [hsum]
  field_simp [(gap_count_pos p).ne', (compositionMarginalVariance_pos p).ne']

theorem compactZ_pos {p : ℕ} (hp : 0 < p) (t : ℝ) : 0 < compactZ p t := by
  by_cases ht : t = 0
  · rw [ht, compactZ_zero hp]
    exact zero_lt_one
  · rw [compactZ_eq_G hp ht]
    exact G_pos hp (compactKappa_pos hp) ht

private theorem hasDerivAt_compactZ_family {p : ℕ} (hp : 0 < p) (k : ℕ) (t : ℝ) :
    HasDerivAt (integralMarginalDerivative p (compactKappa p) k)
      (integralMarginalDerivative p (compactKappa p) (k + 1) t) t := by
  rw [compactKappa_eq_varianceHalf hp]
  simpa [affineMarginalJet] using (continuedMarginalJet_isAt p k 0 1 0 t).2.1

/-- Every derivative of the continued marginal has the same integral representation. -/
theorem iteratedDeriv_compactZ_eq_integral {p : ℕ} (hp : 0 < p) (k : ℕ) :
    iteratedDeriv k (compactZ p) = integralMarginalDerivative p (compactKappa p) k := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_compactZ_family hp k t).deriv

theorem compositionMoment_eq_compactZ {p : ℕ} (hp : 0 < p) (t : ℝ) :
    compositionMoment p 0 t = compactKappa p * t ^ 2 * compactZ p t := by
  by_cases ht : t = 0
  · subst t
    simp [compositionMoment, (gap_count_pos p).ne']
  · rw [compactZ_eq_G hp ht, G, mul_div_cancel₀ _
      (mul_ne_zero (compactKappa_pos hp).ne' (pow_ne_zero _ ht))]

/-- The finite geometric formula for the continued marginal off the collision. -/
theorem compactZ_eq_repeated_geometric {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    let h : ℝ := 3 / (p : ℝ)
    let c := (3 + h) * (3 + 2 * h) / 2
    compactZ p t = (1 - upperTailLambda h t) /
      (c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)) * (compactKappa p * t ^ 2)) := by
  dsimp only
  let h : ℝ := 3 / (p : ℝ)
  let c := (3 + h) * (3 + 2 * h) / 2
  let a := Real.exp (-t / (p : ℝ))
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hgap : upperTailGap h t ≠ 0 := by
    intro hzero
    have he : 1 - Real.exp (-(h * t)) = 0 := by
      rw [tail_gap_factor hh, hzero, mul_zero]
    have harg : -(h * t) = 0 :=
      Real.exp_injective (by rw [Real.exp_zero]; exact (sub_eq_zero.mp he).symm)
    exact (mul_ne_zero hh.ne' ht) (neg_eq_zero.mp harg)
  have hweight : DimThree.defect p a a 1 =
      ((p + 2).choose 2 : ℝ) * Real.exp (-(2 * t)) * compositionMoment p 0 t := by
    rw [UniformThreeSpectrum.defect_cycle_all p 1 a a]
    have hweight := upperTail_lower_weight hp (-t) t
    dsimp only at hweight
    rw [add_neg_cancel, neg_zero, zero_div, Real.exp_zero, neg_neg,
      show 3 * t + -t = 2 * t by ring] at hweight
    exact hweight
  have hexact := upperTail_repeated_defect hp t
  change (1 - a ^ 3) ^ 2 * DimThree.defect p a a 1 = 1 - upperTailLambda h t at hexact
  have ha : a ^ 3 = Real.exp (-(h * t)) := (tail_cube_pow hp t).1
  rw [ha, tail_gap_factor hh, hweight, compositionMoment_eq_compactZ hp] at hexact
  have hc : ((p + 2).choose 2 : ℝ) * h ^ 2 = c := tail_choose_scale hp
  have hc₀ : 0 < c := by dsimp [c]; positivity
  have hden : c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)) * (compactKappa p * t ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc₀.ne' (pow_ne_zero _ hgap))
      (Real.exp_pos _).ne') (mul_ne_zero (compactKappa_pos hp).ne' (pow_ne_zero _ ht))
  change compactZ p t = (1 - upperTailLambda h t) /
    (c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)) * (compactKappa p * t ^ 2))
  apply (eq_div_iff hden).2
  rw [← hexact, ← hc]
  ring

/-- For nonzero arguments the continued marginal is a finite exponential quotient.
This form uses the same positive-rate gap as the Taylor enclosures. -/
theorem compactZ_eq_exp_quotient {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    let h : ℝ := 3 / (p : ℝ)
    let c := (3 + h) * (3 + 2 * h) / 2
    let b := (Real.exp (h * t) - 1) / h
    compactZ p t =
      (Real.exp (-t) * (Real.exp ((3 + 2 * h) * t) - 1 - (3 + 2 * h) * b) /
          (c * b ^ 2) - 1) /
        (compactKappa p * t ^ 2) := by
  dsimp only
  let h : ℝ := 3 / (p : ℝ)
  let c := (3 + h) * (3 + 2 * h) / 2
  let b := (Real.exp (h * t) - 1) / h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hb : b ≠ 0 := by
    intro hb
    have he : Real.exp (h * t) - 1 = 0 := by
      simpa [b, div_eq_zero_iff, hh.ne'] using hb
    exact (mul_ne_zero hh.ne' ht)
      (Real.exp_injective (by rw [Real.exp_zero]; exact sub_eq_zero.mp he))
  have hgap : upperTailGap h t = b * Real.exp (-(h * t)) := by
    unfold upperTailGap b
    rw [Real.exp_neg]
    field_simp [hh.ne', (Real.exp_pos (h * t)).ne']
  have hscale : Real.exp (h * t) = 1 + h * b := by
    dsimp [b]
    field_simp [hh.ne']
    ring
  have htail :
      (1 + (3 + h) * upperTailGap h t) * Real.exp (-((3 + h) * t)) =
        (1 + (3 + 2 * h) * b) * Real.exp (-((3 + 2 * h) * t)) := by
    rw [hgap,
      show -((3 + h) * t) = h * t + -((3 + 2 * h) * t) by ring, Real.exp_add]
    have he : Real.exp (-(h * t)) * Real.exp (h * t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = (Real.exp (h * t) + (3 + h) * b *
          (Real.exp (-(h * t)) * Real.exp (h * t))) *
            Real.exp (-((3 + 2 * h) * t)) := by ring
      _ = _ := by rw [he, hscale]; ring
  have hmass :
      c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)) =
        c * b ^ 2 * Real.exp (-((2 + 2 * h) * t)) := by
    rw [hgap, mul_pow, ← Real.exp_nat_mul]
    push_cast
    calc
      _ = c * b ^ 2 * (Real.exp (2 * -(h * t)) * Real.exp (-(2 * t))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        exact congrArg (fun x : ℝ ↦ c * b ^ 2 * Real.exp x) (by ring)
  have hbmass : c * b ^ 2 ≠ 0 := mul_ne_zero hc.ne' (pow_ne_zero _ hb)
  change compactZ p t =
    (Real.exp (-t) * (Real.exp ((3 + 2 * h) * t) - 1 - (3 + 2 * h) * b) /
        (c * b ^ 2) - 1) / (compactKappa p * t ^ 2)
  rw [compactZ_eq_repeated_geometric hp ht]
  change (1 - ((1 + (3 + h) * upperTailGap h t) * Real.exp (-((3 + h) * t)) +
      c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)))) /
      (c * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t)) * (compactKappa p * t ^ 2)) = _
  rw [htail, hmass]
  have hprod : Real.exp (-t) * Real.exp (-((2 + 2 * h) * t)) =
      Real.exp (-((3 + 2 * h) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp ((3 + 2 * h) * t) * Real.exp (-((3 + 2 * h) * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  let mass := c * b ^ 2 * Real.exp (-((2 + 2 * h) * t))
  have hquot :
      (1 - ((1 + (3 + 2 * h) * b) * Real.exp (-((3 + 2 * h) * t)) + mass)) / mass =
        Real.exp (-t) * (Real.exp ((3 + 2 * h) * t) - 1 - (3 + 2 * h) * b) /
          (c * b ^ 2) - 1 := by
    apply (div_eq_iff (mul_ne_zero hbmass (Real.exp_pos _).ne')).2
    calc
      _ = (Real.exp ((3 + 2 * h) * t) - 1 - (3 + 2 * h) * b) *
            Real.exp (-((3 + 2 * h) * t)) - mass := by
        linear_combination -hinv
      _ = _ := by
        rw [← hprod]
        dsimp [mass]
        field_simp [hbmass]
  rw [← div_div, hquot]

/-- The derivative of the continued marginal in the geometric coordinates. -/
theorem deriv_compactZ_eq_exp_quotient {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    let h : ℝ := 3 / (p : ℝ)
    let k := 3 + 2 * h
    let c := (3 + h) * k / 2
    let b := (Real.exp (h * t) - 1) / h
    let prefactor := Real.exp (-t) / (c * b ^ 2)
    let numerator := Real.exp (k * t) - 1 - k * b
    let decay := -1 - 2 * Real.exp (h * t) / b
    deriv (compactZ p) t =
      (prefactor * (k * (Real.exp (k * t) - Real.exp (h * t)) + decay * numerator) -
        2 * (prefactor * numerator - 1) / t) / (compactKappa p * t ^ 2) := by
  dsimp only
  let h : ℝ := 3 / (p : ℝ)
  let k := 3 + 2 * h
  let c := (3 + h) * k / 2
  let B (s : ℝ) := (Real.exp (h * s) - 1) / h
  let C (s : ℝ) := Real.exp (-s) / (c * B s ^ 2)
  let N (s : ℝ) := Real.exp (k * s) - 1 - k * B s
  let decay := -1 - 2 * Real.exp (h * t) / B t
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hc : 0 < c := by dsimp [c, k]; positivity
  have hb : B t ≠ 0 := by
    intro hb
    have he : Real.exp (h * t) - 1 = 0 := by
      simpa [B, div_eq_zero_iff, hh.ne'] using hb
    exact (mul_ne_zero hh.ne' ht)
      (Real.exp_injective (by rw [Real.exp_zero]; exact sub_eq_zero.mp he))
  have hB : HasDerivAt B (Real.exp (h * t)) t := by
    have hB := ((((hasDerivAt_id' t).const_mul h).exp).sub_const 1).div_const h
    refine hB.congr_deriv ?_
    simp only [mul_one]
    field_simp [hh.ne']
  have hC : HasDerivAt C (C t * decay) t := by
    have he := (hasDerivAt_id' t).neg.exp
    have hden := (hB.pow 2).const_mul c
    refine (he.div hden (mul_ne_zero hc.ne' (pow_ne_zero _ hb))).congr_deriv ?_
    dsimp [C, decay]
    field_simp [hc.ne', hb]
    <;> ring
  have hN : HasDerivAt N (k * (Real.exp (k * t) - Real.exp (h * t))) t := by
    have hN := ((((hasDerivAt_id' t).const_mul k).exp).sub_const 1).sub (hB.const_mul k)
    refine hN.congr_deriv ?_
    simp only [mul_one]
    ring
  have hscale : compactKappa p * t ^ 2 ≠ 0 :=
    mul_ne_zero (compactKappa_pos hp).ne' (pow_ne_zero _ ht)
  have hquot := (((hC.mul hN).sub_const 1).div (((hasDerivAt_id' t).pow 2).const_mul
    (compactKappa p)) hscale)
  have hnear :
      compactZ p =ᶠ[𝓝 t] fun s ↦ (C s * N s - 1) / (compactKappa p * s ^ 2) := by
    filter_upwards [eventually_ne_nhds ht] with s hs
    rw [compactZ_eq_exp_quotient hp hs]
    simp only [C, B, N, c, k, h]
    ring
  rw [(hquot.congr_of_eventuallyEq hnear).deriv]
  change _ = (C t * (k * (Real.exp (k * t) - Real.exp (h * t)) + decay * N t) -
      2 * (C t * N t - 1) / t) / (compactKappa p * t ^ 2)
  simp only [Pi.mul_apply, Pi.pow_apply]
  field_simp [(compactKappa_pos hp).ne', ht]
  <;> ring

/-- The logarithmic slope of the normalized marginal. -/
def compactZSlope (p : ℕ) : ℝ → ℝ := marginalLogSlope (compactZ p)

theorem compactZSlope_eq {p : ℕ} (hp : 0 < p) (t : ℝ) :
    compactZSlope p t = integralMarginalDerivative p (compactKappa p) 1 t / compactZ p t := by
  have h : deriv (compactZ p) t = integralMarginalDerivative p (compactKappa p) 1 t :=
    (hasDerivAt_compactZ_family hp 0 t).deriv
  simp only [compactZSlope, marginalLogSlope, h]

private theorem hasDerivAt_compactZSlope {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (compactZSlope p)
      (integralMarginalDerivative p (compactKappa p) 2 t / compactZ p t -
        compactZSlope p t ^ 2) t := by
  have h := (hasDerivAt_compactZ_family hp 1 t).fun_div
    (hasDerivAt_compactZ_family hp 0 t) (compactZ_pos hp t).ne'
  apply (h.congr_of_eventuallyEq (Eventually.of_forall (compactZSlope_eq hp))).congr_deriv
  rw [compactZSlope_eq hp]
  change (_ - _) / compactZ p t ^ 2 = _ / compactZ p t - (_ / compactZ p t) ^ 2
  field_simp [(compactZ_pos hp t).ne']
  rfl

/-- The slope derivative in the form evaluated by the radical comparison. -/
theorem deriv_compactZSlope {p : ℕ} (hp : 0 < p) (t : ℝ) :
    deriv (compactZSlope p) t =
      integralMarginalDerivative p (compactKappa p) 2 t / compactZ p t -
        compactZSlope p t ^ 2 :=
  (hasDerivAt_compactZSlope hp t).deriv

private theorem hasDerivAt_marginal_factor {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (compositionMoment p 0)
      (compactKappa p * (2 * t) * compactZ p t +
        (compactKappa p * t ^ 2) * integralMarginalDerivative p (compactKappa p) 1 t) t := by
  have ht : HasDerivAt (fun x : ℝ ↦ compactKappa p * x ^ 2)
      (compactKappa p * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (compactKappa p)
  exact (ht.fun_mul (hasDerivAt_compactZ_family hp 0 t)).congr_of_eventuallyEq
    (Eventually.of_forall (compositionMoment_eq_compactZ hp))

theorem marginalLogSlope_eq_compactZSlope {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    marginalLogSlope (compositionMoment p 0) t = 2 / t + compactZSlope p t := by
  rw [marginalLogSlope, (hasDerivAt_marginal_factor hp t).deriv,
    compositionMoment_eq_compactZ hp t, compactZSlope_eq hp]
  field_simp [(compactKappa_pos hp).ne', (compactZ_pos hp t).ne', ht]

theorem reflectedHalfLogSlope_eq_compactZSlope {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    reflectedHalfLogSlope (compositionMoment p 0) t = 1 / t - compactZSlope p (-t) / 2 := by
  have hR := (hasDerivAt_marginal_factor hp (-t)).differentiableAt.hasDerivAt
  have hs := hR.comp t ((hasDerivAt_id' t).neg)
  change HasDerivAt (fun x ↦ compositionMoment p 0 (-x))
    (deriv (compositionMoment p 0) (-t) * (-1)) t at hs
  have heq : reflectedHalfLogSlope (compositionMoment p 0) t =
      -marginalLogSlope (compositionMoment p 0) (-t) / 2 := by
    rw [reflectedHalfLogSlope, hs.deriv, marginalLogSlope, mul_neg_one, neg_div]
  rw [heq, marginalLogSlope_eq_compactZSlope hp (neg_ne_zero.mpr ht), div_neg]
  ring

theorem deriv_marginalLogSlope_eq_compactZSlope {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    deriv (marginalLogSlope (compositionMoment p 0)) t =
      -2 / t ^ 2 + deriv (compactZSlope p) t := by
  have h₁ : HasDerivAt (fun x : ℝ ↦ 2 / x) (-2 / t ^ 2) t := by
    convert (hasDerivAt_inv ht).const_mul 2 using 1 <;> simp [div_eq_mul_inv, mul_neg]
  have h₂ := (hasDerivAt_compactZSlope hp t).differentiableAt.hasDerivAt
  have hEq : marginalLogSlope (compositionMoment p 0) =ᶠ[𝓝 t]
      (fun x ↦ 2 / x + compactZSlope p x) := by
    filter_upwards [eventually_ne_nhds ht] with x hx using marginalLogSlope_eq_compactZSlope hp hx
  exact ((h₁.fun_add h₂).congr_of_eventuallyEq hEq).deriv

private theorem sqrt_marginals_eq_compactZ {p : ℕ} (hp : 0 < p) {v d : ℝ}
    (hv : 0 ≤ v) (hd : 0 ≤ d) :
    Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 d) =
      compactKappa p * v * d * Real.sqrt (compactZ p v * compactZ p d) := by
  have heq : compositionMoment p 0 v * compositionMoment p 0 d =
      (compactKappa p * v * d) ^ 2 * (compactZ p v * compactZ p d) := by
    rw [compositionMoment_eq_compactZ hp v, compositionMoment_eq_compactZ hp d]
    ring
  rw [heq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (mul_nonneg (mul_nonneg (compactKappa_pos hp).le hv) hd)]

/-- The radical expression with the quadratic zero at the gap removed. -/
def compactRegularizedQ (p : ℕ) (u v : ℝ) : ℝ :=
  let d := v - u
  let s := compactZSlope p
  let x := s d - s (-u)
  let y := s v + s d + s (-v)
  show ℝ from -compactKappa p * v * Real.sqrt (compactZ p v * compactZ p d) *
    (1 / u + (x + y) / 2 + d * (y / (2 * u) + x * y / 4 + deriv s d / 2))

/-- The singular mixed radical equals the regularized expression on the ordered chamber. -/
theorem compactMixedQ_eq_regularized {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    compactMixedQ p u v = compactRegularizedQ p u v := by
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  dsimp only [compactMixedQ, compactRegularizedQ]
  rw [sqrt_marginals_eq_compactZ hp hv.le hd.le,
    reflectedHalfLogSlope_eq_compactZSlope hp hu.ne',
    reflectedHalfLogSlope_eq_compactZSlope hp hv.ne',
    marginalLogSlope_eq_compactZSlope hp hd.ne',
    marginalLogSlope_eq_compactZSlope hp hv.ne',
    deriv_marginalLogSlope_eq_compactZSlope hp hd.ne']
  have hleft : 2 / (v - u) + compactZSlope p (v - u) +
      2 * (1 / u - compactZSlope p (-u) / 2) =
      2 * (1 / u + 1 / (v - u)) + (compactZSlope p (v - u) - compactZSlope p (-u)) := by ring
  have hright : 2 / v + compactZSlope p v + (2 / (v - u) + compactZSlope p (v - u)) -
      2 * (1 / v - compactZSlope p (-v) / 2) =
      2 / (v - u) + (compactZSlope p v + compactZSlope p (v - u) + compactZSlope p (-v)) := by ring
  rw [hleft, hright]
  generalize compactZSlope p (v - u) - compactZSlope p (-u) = x
  generalize compactZSlope p v + compactZSlope p (v - u) + compactZSlope p (-v) = y
  field_simp [hu.ne', hd.ne']
  ring

/-- A positive tangent parameter gives a lower bound for the mixed radical
when its regularized multiplier is nonnegative. -/
theorem compactMixedQ_tangent_lower {p : ℕ} (hp : 0 < p) {u v r : ℝ}
    (hu : 0 < u) (huv : u < v) (hr : 0 < r) :
    let d := v - u
    let s := compactZSlope p
    let x := s d - s (-u)
    let y := s v + s d + s (-v)
    let multiplier := 1 / u + (x + y) / 2 +
      d * (y / (2 * u) + x * y / 4 + deriv s d / 2)
    0 ≤ multiplier →
      -compactKappa p * v * ((compactZ p v * compactZ p d / r + r) / 2) * multiplier ≤
        compactMixedQ p u v := by
  dsimp only
  intro hmultiplier
  let z := compactZ p v * compactZ p (v - u)
  have hz : 0 ≤ z := mul_nonneg (compactZ_pos hp v).le (compactZ_pos hp (v - u)).le
  have htangent : Real.sqrt z ≤ (z / r + r) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (mul_le_mul_iff_right₀ hr).mp
    have hcancel : (z / r) * r = z := div_mul_cancel₀ z hr.ne'
    nlinarith only [sq_nonneg (Real.sqrt z - r), Real.sq_sqrt hz, hcancel]
  have hnegative : -compactKappa p * v ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (compactKappa_pos hp).le) (hu.trans huv).le
  rw [compactMixedQ_eq_regularized hp hu huv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left htangent hnegative) hmultiplier

/-- The regularized expression is continuous at each positive collision. -/
theorem continuousAt_compactRegularizedQ_collision {p : ℕ} (hp : 0 < p) {u : ℝ}
    (hu : 0 < u) : ContinuousAt (fun z : ℝ × ℝ ↦ compactRegularizedQ p z.1 z.2) (u, u) := by
  have hM (k : ℕ) : Continuous (integralMarginalDerivative p (compactKappa p) k) :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_compactZ_family hp k t).continuousAt
  have hZ : Continuous (compactZ p) := hM 0
  have hs : Continuous (compactZSlope p) :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_compactZSlope hp t).continuousAt
  have hw : Continuous (deriv (compactZSlope p)) := by
    rw [funext (deriv_compactZSlope hp)]
    exact ((hM 2).div hZ (fun t ↦ (compactZ_pos hp t).ne')).sub (hs.pow 2)
  have hu' : (u, u).1 ≠ 0 := hu.ne'
  have h₂u : (2 : ℝ) * (u, u).1 ≠ 0 := mul_ne_zero (by norm_num) hu'
  dsimp only [compactRegularizedQ]
  fun_prop

/-- The limit is taken inside the ordered chamber, where the original radical formula applies. -/
theorem tendsto_compactMixedQ_collision {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    Tendsto (compactMixedQ p u) (𝓝[>] u)
      (𝓝 (-compactKappa p * u * Real.sqrt (compactZ p u) *
        (1 / u + compactZSlope p 0 + compactZSlope p u / 2))) := by
  have hvalue : compactRegularizedQ p u u =
      -compactKappa p * u * Real.sqrt (compactZ p u) *
        (1 / u + compactZSlope p 0 + compactZSlope p u / 2) := by
    simp only [compactRegularizedQ, sub_self, compactZ_zero hp, mul_one, zero_mul, add_zero]
    ring
  rw [← hvalue]
  have h : ContinuousAt (compactRegularizedQ p u) u :=
    (continuousAt_compactRegularizedQ_collision hp hu).comp
      (continuous_const.prodMk continuous_id).continuousAt
  refine (tendsto_congr' ?_).2 h.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi u)] with v hv
  exact compactMixedQ_eq_regularized hp hu hv

/-- The existing Taylor model controls the continued marginal and its derivatives through zero. -/
theorem iteratedDeriv_compactZ_sub_taylor_le {p k : ℕ} (hp : 0 < p) (hk : k ≤ 4)
    {t : ℝ} (ht : |t| ≤ 1) :
    |iteratedDeriv k (compactZ p) t - marginalTaylorPolynomial p k t| ≤ 1 / (2 : ℝ) ^ 30 := by
  rw [iteratedDeriv_compactZ_eq_integral hp, compactKappa_eq_varianceHalf hp]
  exact integralMarginalDerivative_sub_taylor_le hp hk ht

#print axioms compactZ_zero
#print axioms iteratedDeriv_compactZ_eq_integral
#print axioms deriv_compactZSlope
#print axioms reflectedHalfLogSlope_eq_compactZSlope
#print axioms deriv_marginalLogSlope_eq_compactZSlope
#print axioms compactMixedQ_eq_regularized
#print axioms tendsto_compactMixedQ_collision
#print axioms iteratedDeriv_compactZ_sub_taylor_le

/-- The nonzero marginal quotient with the large exponential factors combined. -/
theorem compactZ_eq_combined_quotient {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    let h : ℝ := 3 / (p : ℝ)
    let k := 3 + 2 * h
    let c := (3 + h) * k / 2
    let b := (Real.exp (h * t) - 1) / h
    let numerator := Real.exp ((2 + 2 * h) * t) - Real.exp (-t) * (1 + k * b)
    compactZ p t = (numerator / (c * b ^ 2) - 1) / (compactKappa p * t ^ 2) := by
  dsimp only
  rw [compactZ_eq_exp_quotient hp ht]
  rw [show (2 + 2 * (3 / (p : ℝ))) * t = -t + (3 + 2 * (3 / (p : ℝ))) * t by ring,
    Real.exp_add]
  ring

/-- The differentiated quotient with the same combined exponentials. -/
theorem deriv_compactZ_eq_combined_quotient {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    let h : ℝ := 3 / (p : ℝ)
    let k := 3 + 2 * h
    let c := (3 + h) * k / 2
    let b := (Real.exp (h * t) - 1) / h
    let upper := Real.exp ((2 + 2 * h) * t)
    let lower := Real.exp (-t)
    let numerator := upper - lower * (1 + k * b)
    let first := (2 + 2 * h) * upper + lower * (1 + k * b - k * Real.exp (h * t))
    let marginal := numerator / (c * b ^ 2) - 1
    deriv (compactZ p) t =
      ((first - 2 * Real.exp (h * t) / b * numerator) / (c * b ^ 2) -
        2 * marginal / t) / (compactKappa p * t ^ 2) := by
  dsimp only
  rw [deriv_compactZ_eq_exp_quotient hp ht]
  rw [show (2 + 2 * (3 / (p : ℝ))) * t = -t + (3 + 2 * (3 / (p : ℝ))) * t by ring,
    Real.exp_add]
  simp only [div_eq_mul_inv]
  ring

/-- The quadratic exponential remainder divided by `t ^ 2`, continued at `t = 0`. -/
def regularizedMarginalRemainder (t : ℝ) : ℝ → ℝ :=
  if t = 0 then (fun x ↦ x ^ 2 / 2) else (fun x ↦ (Real.exp (t * x) - 1 - t * x) / t ^ 2)

private theorem contDiff_regularizedMarginalRemainder (t : ℝ) :
    ContDiff ℝ ⊤ (regularizedMarginalRemainder t) := by
  by_cases ht : t = 0 <;>
    simp only [regularizedMarginalRemainder, ht, ite_true, ite_false] <;> fun_prop

/-- For fixed `t`, the regularized marginal integrand is smooth in the spatial variable. -/
theorem contDiff_regularizedMarginalIntegrand (h t : ℝ) :
    ContDiff ℝ ⊤ (fun x ↦ (2 + h - x) * regularizedMarginalRemainder t x) :=
  (show ContDiff ℝ ⊤ (fun x : ℝ ↦ 2 + h - x) by fun_prop).mul
    (contDiff_regularizedMarginalRemainder t)

/-- The sixth spatial derivative of the weighted, regularized marginal integrand. -/
theorem iteratedDeriv_six_regularizedMarginalIntegrand (h t x : ℝ) :
    iteratedDeriv 6 (fun y ↦ (2 + h - y) * regularizedMarginalRemainder t y) x =
      t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6) := by
  let first (y : ℝ) := if t = 0 then y else (Real.exp (t * y) - 1) / t
  have hfirst : deriv (regularizedMarginalRemainder t) = first := by
    funext y
    apply HasDerivAt.deriv
    by_cases ht : t = 0
    · simp only [regularizedMarginalRemainder, first, ht, ite_true]
      exact (((hasDerivAt_id' y).fun_pow 2).div_const 2).congr_deriv (by norm_num <;> ring)
    · simp only [regularizedMarginalRemainder, first, ht, ite_false]
      have hd := (hasDerivAt_id' y).const_mul t
      refine (((hd.exp.sub_const 1).fun_sub hd).div_const (t ^ 2)).congr_deriv ?_
      field_simp [ht] <;> ring
  have hsecond : deriv first = fun y ↦ Real.exp (t * y) := by
    funext y
    apply HasDerivAt.deriv
    by_cases ht : t = 0
    · simpa only [first, ht, ite_true, zero_mul, Real.exp_zero] using hasDerivAt_id' y
    · simp only [first, ht, ite_false]
      have hd := (hasDerivAt_id' y).const_mul t
      refine ((hd.exp.sub_const 1).div_const t).congr_deriv ?_
      field_simp [ht] <;> ring
  have hderiv (n : ℕ) : iteratedDeriv (n + 2) (regularizedMarginalRemainder t) =
      fun y ↦ t ^ n * Real.exp (t * y) := by
    rw [show n + 2 = (n + 1) + 1 by rfl, iteratedDeriv_succ', hfirst,
      iteratedDeriv_succ', hsecond, iteratedDeriv_exp_const_mul]
  have hAffine (n : ℕ) : iteratedDeriv n (fun y : ℝ ↦ 2 + h - y) x =
      if n = 0 then 2 + h - x else if n = 1 then -1 else 0 := by
    cases n with
    | zero => simp
    | succ n =>
      rw [iteratedDeriv_succ', deriv_const_sub_id', iteratedDeriv_const] <;>
        cases n <;> simp
  have h₅ : iteratedDeriv 5 (regularizedMarginalRemainder t) x =
      t ^ 3 * Real.exp (t * x) := congrFun (hderiv 3) x
  have h₆ : iteratedDeriv 6 (regularizedMarginalRemainder t) x =
      t ^ 4 * Real.exp (t * x) := congrFun (hderiv 4) x
  have hA : ContDiffAt ℝ 6 (fun y : ℝ ↦ 2 + h - y) x := by fun_prop
  have hT : ContDiffAt ℝ 6 (regularizedMarginalRemainder t) x :=
    ((contDiff_regularizedMarginalRemainder t).of_le le_top).contDiffAt
  rw [iteratedDeriv_fun_mul hA hT]
  norm_num [Finset.sum_range_succ, Nat.choose, hAffine, h₅, h₆] <;> ring

end RefinedBMV.PositiveCenter
