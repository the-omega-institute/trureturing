/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactRegularizedRadical
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Collision regularization of the normalized mixed radical. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMarginalTaylor

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

end RefinedBMV.PositiveCenter
