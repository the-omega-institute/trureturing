/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourRadicalAverage
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A divided-difference bound for the decreasing radical density at gap four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSeparatedGapRadical
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.MGFAnalytic

/-! # Divided differences of the radical density at gap four -/

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private sub_le_sub_of_derivatives radicalRateFactor radicalRateFactorDeriv
  hasDerivAt_radicalRateFactor upperTailRadicalRoot_pos hasDerivAt_upperTailRadicalRoot
  hasDerivAt_radicalRootDeriv from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSeparatedGapRadical

open private collisionInner collisionInner_eq collisionInner_pos from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterCollisionRadicand

/-- Pair each point in the lower half with its reflection in the midpoint. -/
private theorem midpoint_moment_nonneg {T : ℝ → ℝ} {d v : ℝ} (hdv : d ≤ v)
    (hT : ContinuousOn T (Icc d v)) (hanti : AntitoneOn T (Icc d v)) :
    0 ≤ ∫ t in d..v, ((d + v) / 2 - t) * T t := by
  let c := (d + v) / 2
  let g (t : ℝ) := (c - t) * T t
  have hdc : d ≤ c := by dsimp [c]; linarith
  have hcv : c ≤ v := by dsimp [c]; linarith
  have hcenter : d + v = 2 * c := by dsimp [c]; ring
  have hg : ContinuousOn g (Icc d v) := (continuousOn_const.sub continuousOn_id).mul hT
  have hgLeft : ContinuousOn g (Icc d c) :=
    hg.mono (Icc_subset_Icc le_rfl hcv)
  have hgRight : ContinuousOn g (Icc c v) :=
    hg.mono (Icc_subset_Icc hdc le_rfl)
  have hreflect (t : ℝ) (ht : t ∈ Icc d c) : d + v - t ∈ Icc d v := by
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hgReflect : ContinuousOn (fun t ↦ g (d + v - t)) (Icc d c) :=
    hg.comp' (by fun_prop) (fun t ht ↦ hreflect t ht)
  have hsubstitution :
      (∫ t in d..c, g (d + v - t)) = ∫ t in c..v, g t := by
    simpa only [show d + v - c = c by linarith, show d + v - d = v by ring] using
      (intervalIntegral.integral_comp_sub_left (f := g) (a := d) (b := c) (d + v))
  have hpair (t : ℝ) (ht : t ∈ Icc d c) : 0 ≤ g t + g (d + v - t) := by
    have horder : t ≤ d + v - t := by linarith [ht.2]
    have hweights := hanti (show t ∈ Icc d v from ⟨ht.1, ht.2.trans hcv⟩)
      (hreflect t ht) horder
    calc
      0 ≤ (c - t) * (T t - T (d + v - t)) :=
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hweights)
      _ = g t + g (d + v - t) := by dsimp [g]; rw [hcenter]; ring
  change 0 ≤ ∫ t in d..v, g t
  calc
    0 ≤ ∫ t in d..c, g t + g (d + v - t) := intervalIntegral.integral_nonneg hdc hpair
    _ = (∫ t in d..c, g t) + ∫ t in c..v, g t := by
      rw [intervalIntegral.integral_add (hgLeft.intervalIntegrable_of_Icc hdc)
        (hgReflect.intervalIntegrable_of_Icc hdc), hsubstitution]
    _ = ∫ t in d..v, g t := intervalIntegral.integral_add_adjacent_intervals
      (hgLeft.intervalIntegrable_of_Icc hdc) (hgRight.intervalIntegrable_of_Icc hcv)

private theorem reciprocal_sub_le_tangent {d c t : ℝ}
    (hd : 0 < d) (hc : 0 < c) (ht : 0 < t) :
    3 / d - 3 / t ≤ (3 / d - 3 / c) + (3 / c ^ 2) * (t - c) := by
  have hidentity : (3 / d - 3 / c) + (3 / c ^ 2) * (t - c) - (3 / d - 3 / t) =
      3 * (t - c) ^ 2 / (t * c ^ 2) := by
    field_simp [hd.ne', hc.ne', ht.ne'] <;> ring
  apply sub_nonneg.mp
  rw [hidentity]
  positivity

/-- The midpoint bounds the difference between the left logarithmic slope
and the normalized divided difference. -/
theorem separatedFour_radical_dividedDifference_average {T : ℝ → ℝ} {d v : ℝ}
    (hd : 4 ≤ d) (hdv : d < v)
    (hTpos : ∀ t ∈ Icc d v, 0 < T t)
    (hTdiff : ∀ t ∈ Icc d v, DifferentiableAt ℝ T t)
    (hrhoDiff : ∀ t ∈ Icc d v, DifferentiableAt ℝ (fun s ↦ deriv T s / T s) t)
    (hrhoUpper : ∀ t ∈ Icc d v, deriv T t / T t ≤ -(17 / 12 : ℝ))
    (hrhoCurv : ∀ t ∈ Icc d v, -(3 : ℝ) / t ^ 2 ≤ deriv (fun s ↦ deriv T s / T s) t) :
    deriv T d / T d - (T v - T d) / (∫ t in d..v, T t) ≤ 3 * (v - d) / (d * (d + v)) := by
  let rho (t : ℝ) := deriv T t / T t
  let c := (d + v) / 2
  let K := 3 * (v - d) / (d * (d + v))
  have hd₀ : 0 < d := by linarith
  have hsum : 0 < d + v := by linarith
  have hc₀ : 0 < c := by dsimp [c]; linarith
  have hK : 3 / d - 3 / c = K := by
    dsimp [c, K]
    field_simp [hd₀.ne', hsum.ne'] <;> ring
  have hTDeriv (t : ℝ) (ht : t ∈ Icc d v) : HasDerivAt T (rho t * T t) t :=
    (hTdiff t ht).hasDerivAt.congr_deriv (by
      dsimp only [rho]
      rw [div_mul_cancel₀ _ (hTpos t ht).ne'])
  have hTcont : ContinuousOn T (Icc d v) :=
    fun t ht ↦ (hTdiff t ht).continuousAt.continuousWithinAt
  have hrhoCont : ContinuousOn rho (Icc d v) :=
    fun t ht ↦ (hrhoDiff t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn T (Icc d v) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc d v) hTcont
    · exact fun t ht ↦ (hTdiff t (interior_subset ht)).differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hTDeriv t ht').deriv]
      have hneg : rho t ≤ 0 := le_trans (hrhoUpper t ht') (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg hneg (hTpos t ht').le
  have hrecip (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s : ℝ ↦ 3 / s) (-(3 : ℝ) / t ^ 2) t := by
    apply ((hasDerivAt_const t (3 : ℝ)).div (hasDerivAt_id' t) ht.ne').congr_deriv
    simp
  have hpoint (t : ℝ) (ht : t ∈ Icc d v) : rho d - rho t ≤ 3 / d - 3 / t := by
    have hsub (s : ℝ) (hs : s ∈ Icc d t) : s ∈ Icc d v := ⟨hs.1, hs.2.trans ht.2⟩
    have h := sub_le_sub_of_derivatives ht.1
      (fun s hs ↦ hrecip s (hd₀.trans_le hs.1))
      (fun s hs ↦ (hrhoDiff s (hsub s hs)).hasDerivAt)
      (fun s hs ↦ hrhoCurv s (hsub s hs))
    change 3 / t - 3 / d ≤ rho t - rho d at h
    linarith only [h]
  have hD : 0 < ∫ t in d..v, T t := intervalIntegral.integral_pos hdv hTcont
    (fun t ht ↦ (hTpos t (Ioc_subset_Icc_self ht)).le)
    ⟨d, left_mem_Icc.mpr hdv.le, hTpos d (left_mem_Icc.mpr hdv.le)⟩
  have hscaled : ContinuousOn (fun t ↦ (rho d - K) * T t) (Icc d v) :=
    continuousOn_const.mul hTcont
  have hprod : ContinuousOn (fun t ↦ rho t * T t) (Icc d v) := hrhoCont.mul hTcont
  have htangent : ContinuousOn (fun t ↦ (-(3 / c ^ 2)) * ((c - t) * T t)) (Icc d v) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).mul hTcont)
  have hFTC : (∫ t in d..v, rho t * T t) = T v - T d :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hdv.le hTcont
      (fun t ht ↦ hTDeriv t (Ioo_subset_Icc_self ht)) (hprod.intervalIntegrable_of_Icc hdv.le)
  have hmean : (rho d - K) * (∫ t in d..v, T t) - (T v - T d) ≤ 0 := by
    calc
      _ = ∫ t in d..v, (rho d - K) * T t - rho t * T t := by
        symm
        calc
          _ = (∫ t in d..v, (rho d - K) * T t) - ∫ t in d..v, rho t * T t :=
            intervalIntegral.integral_sub (hscaled.intervalIntegrable_of_Icc hdv.le)
              (hprod.intervalIntegrable_of_Icc hdv.le)
          _ = _ := by rw [intervalIntegral.integral_const_mul, hFTC]
      _ ≤ ∫ t in d..v, (-(3 / c ^ 2)) * ((c - t) * T t) := by
        apply intervalIntegral.integral_mono_on hdv.le
          ((hscaled.sub hprod).intervalIntegrable_of_Icc hdv.le)
          (htangent.intervalIntegrable_of_Icc hdv.le)
        intro t ht
        change (rho d - K) * T t - rho t * T t ≤ -(3 / c ^ 2) * ((c - t) * T t)
        have h := (hpoint t ht).trans (reciprocal_sub_le_tangent hd₀ hc₀ (hd₀.trans_le ht.1))
        rw [hK] at h
        calc
          _ = (rho d - rho t - K) * T t := by ring
          _ ≤ ((3 / c ^ 2) * (t - c)) * T t :=
            mul_le_mul_of_nonneg_right (by linarith only [h]) (hTpos t ht).le
          _ = _ := by ring
      _ ≤ 0 := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
          (midpoint_moment_nonneg hdv.le hTcont hanti)
  have hquot := (le_div_iff₀ hD).mpr (sub_nonpos.mp hmean)
  change rho d - (T v - T d) / (∫ t in d..v, T t) ≤ K
  linarith only [hquot]

private theorem radicalRateFactor_pos_of_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < radicalRateFactor h t := by
  change 0 < (1 + h) * upperTailGap h t - 1 + Real.exp (-((1 + h) * t))
  rw [collisionInner_eq hh]
  exact mul_pos (mul_pos (by positivity) (pow_pos ht 2)) (collisionInner_pos h t)

/-- In the fixed-square representation of the normalized rate factor, the
  rate is `-x * (h + y)` and the density is `x`. The second derivative of
  its log integral is the variance of this rate under exponential tilt. -/
private theorem radicalRate_logSlope_variance {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    ∃ k : ℝ, -(2 : ℝ) / t ^ 2 ≤ k ∧
      HasDerivAt (fun s ↦ radicalRateFactorDeriv h s / radicalRateFactor h s) k t := by
  let I := Ioc (0 : ℝ) 1
  let unitMeasure := (volume : Measure ℝ).restrict I
  let μ := unitMeasure.prod unitMeasure
  let w (p : ℝ × ℝ) := ENNReal.ofReal p.1
  let ν := μ.withDensity w
  let X (p : ℝ × ℝ) := -(p.1 * (h + p.2))
  let C := cgf X ν
  have hμ : μ = (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ I) := by
    exact (Measure.prod_restrict I I).trans (by rw [Measure.volume_eq_prod])
  have hweight : Measurable w := measurable_fst.ennreal_ofReal
  have hfinite : ∀ᵐ p ∂μ, w p < ⊤ := Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
  have hw : (fun p ↦ (w p).toReal) =ᵐ[μ] fun p ↦ p.1 := by
    rw [hμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact ENNReal.toReal_ofReal hp.1.1.le
  have hi (s : ℝ) : Integrable (fun p ↦ p.1 * Real.exp (s * X p)) μ := by
    rw [hμ]
    have hc : Continuous (fun p : ℝ × ℝ ↦ p.1 * Real.exp (s * X p)) := by
      dsimp only [X]
      fun_prop
    have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    exact (hc.continuousOn.integrableOn_compact hcompact).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hae (s : ℝ) : (fun p ↦ (w p).toReal • Real.exp (s * X p)) =ᵐ[μ]
      fun p ↦ p.1 * Real.exp (s * X p) := by
    filter_upwards [hw] with p hp
    change (w p).toReal = p.1 at hp
    rw [smul_eq_mul, hp]
  have hinterior : interior (integrableExpSet X ν) = univ := by
    rw [show integrableExpSet X ν = univ by
      apply eq_univ_of_forall
      intro s
      change Integrable (fun p ↦ Real.exp (s * X p)) ν
      exact (integrable_withDensity_iff_integrable_smul' hweight hfinite).mpr
        ((hi s).congr (hae s).symm), interior_univ]
  have hmem (s : ℝ) : s ∈ interior (integrableExpSet X ν) := by rw [hinterior]; trivial
  have hmgf (s : ℝ) : mgf X ν s = collisionInner h s := by
    change (∫ p, Real.exp (s * X p) ∂μ.withDensity w) = _
    rw [integral_withDensity_eq_integral_toReal_smul hweight hfinite, integral_congr_ae (hae s)]
    change (∫ p, p.1 * Real.exp (s * X p) ∂unitMeasure.prod unitMeasure) = _
    rw [integral_prod _ (hi s)]
    unfold collisionInner expGapMean
    simp only [unitMeasure, I, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    apply congrArg (fun f : ℝ → ℝ ↦ ∫ x in Ioc (0 : ℝ) 1, f x)
    funext x
    rw [← integral_const_mul]
    apply congrArg (fun f : ℝ → ℝ ↦ ∫ y in Ioc (0 : ℝ) 1, f y)
    funext y
    change x * Real.exp (s * -(x * (h + y))) =
      x * Real.exp (-(h * s * x)) * Real.exp (-(1 * (s * x) * y))
    rw [show s * -(x * (h + y)) = -(h * s * x) + -(1 * (s * x) * y) by ring,
      Real.exp_add]
    ring
  have hCanalytic (s : ℝ) : AnalyticAt ℝ C s := analyticAt_cgf (hmem s)
  have hlog (s : ℝ) (hs : 0 < s) :
      Real.log (radicalRateFactor h s) = Real.log (1 + h) + 2 * Real.log s + C s := by
    have hj : (1 + h : ℝ) ≠ 0 := by positivity
    have hM : mgf X ν s ≠ 0 := by rw [hmgf]; exact (collisionInner_pos h s).ne'
    change Real.log ((1 + h) * upperTailGap h s - 1 + Real.exp (-((1 + h) * s))) = _
    rw [collisionInner_eq hh, ← hmgf, Real.log_mul (mul_ne_zero hj (pow_ne_zero _ hs.ne')) hM,
      Real.log_mul hj (pow_ne_zero _ hs.ne'), Real.log_pow] <;> simp only [Nat.cast_ofNat, C, cgf]
  have hslope (s : ℝ) (hs : 0 < s) :
      radicalRateFactorDeriv h s / radicalRateFactor h s = 2 * s⁻¹ + deriv C s := by
    have hnear : (fun r ↦ Real.log (radicalRateFactor h r)) =ᶠ[𝓝 s]
        (fun r ↦ Real.log (1 + h) + 2 * Real.log r + C r) := by
      filter_upwards [eventually_gt_nhds hs] with r hr using hlog r hr
    have hright := (((Real.hasDerivAt_log hs.ne').const_mul (2 : ℝ)).const_add
      (Real.log (1 + h))).add (hCanalytic s).differentiableAt.hasDerivAt
    have hleft := (hasDerivAt_radicalRateFactor (t := s) hh).log
      (radicalRateFactor_pos_of_pos hh hs).ne'
    exact hleft.deriv.symm.trans (hright.congr_of_eventuallyEq hnear).deriv
  have hsnear : (fun s ↦ radicalRateFactorDeriv h s / radicalRateFactor h s) =ᶠ[𝓝 t]
      (fun s ↦ 2 * s⁻¹ + deriv C s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs using hslope s hs
  have hcurv : 0 ≤ iteratedDeriv 2 C t := by
    dsimp only [C]
    rw [iteratedDeriv_two_cgf_eq_integral (hmem t)]
    exact div_nonneg (integral_nonneg (fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
      mgf_nonneg
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hcurv
  let k := -(2 : ℝ) / t ^ 2 + deriv (deriv C) t
  refine ⟨k, le_add_of_nonneg_right hcurv, ?_⟩
  have hderiv := ((hasDerivAt_inv ht.ne').const_mul (2 : ℝ)).add
    (hCanalytic t).deriv.differentiableAt.hasDerivAt
  apply (hderiv.congr_of_eventuallyEq hsnear).congr_deriv
  dsimp only [k]
  ring

private theorem radicalRoot_logSlope_curvature {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hupper : deriv (deriv (upperTailRadicalRoot h)) t / deriv (upperTailRadicalRoot h) t ≤ 0) :
    let T := deriv (upperTailRadicalRoot h)
    let rho := fun s ↦ deriv T s / T s
    0 < T t ∧ DifferentiableAt ℝ T t ∧ DifferentiableAt ℝ rho t ∧
      -(3 : ℝ) / t ^ 2 ≤ deriv rho t := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  let rho := fun s ↦ deriv T s / T s
  let R := fun s ↦ -2 + upperTailSlope h s +
    radicalRateFactorDeriv h s / radicalRateFactor h s - T s / z s
  have hTpos (s : ℝ) (hs : 0 < s) : 0 < T s := by
    change 0 < deriv (upperTailRadicalRoot h) s
    rw [(hasDerivAt_upperTailRadicalRoot hh hs).deriv]
    have hH := radicalRateFactor_pos_of_pos hh hs
    have hgap := tail_gap_pos hh hs
    have hz := upperTailRadicalRoot_pos hh hs
    positivity
  have hTd (s : ℝ) (hs : 0 < s) : HasDerivAt T (T s * R s) s :=
    hasDerivAt_radicalRootDeriv hh hs (radicalRateFactor_pos_of_pos hh hs)
  have hnear : rho =ᶠ[𝓝 t] R := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    change deriv T s / T s = R s
    rw [(hTd s hs).deriv, mul_div_cancel_left₀ _ (hTpos s hs).ne']
  have hRnonpos : R t ≤ 0 := by
    have hle : rho t ≤ 0 := hupper
    simpa only [hnear.eq_of_nhds] using hle
  have hzD : HasDerivAt z (T t) t :=
    (hasDerivAt_upperTailRadicalRoot hh ht).differentiableAt.hasDerivAt
  have hz : 0 < z t := upperTailRadicalRoot_pos hh ht
  have hratio := (hTd t ht).div hzD hz.ne'
  have hratioNonpos : (T t * R t * z t - T t * T t) / z t ^ 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hTpos t ht).le hRnonpos) hz.le).trans
        (mul_nonneg (hTpos t ht).le (hTpos t ht).le))
  obtain ⟨k, hklower, hk⟩ := radicalRate_logSlope_variance hh ht
  have hL := hasDerivAt_upperTailSlope hh ht
  have hLbound := (upperTailSlope_bounds hh ht).2.2.2.1
  rw [hL.deriv] at hLbound
  have hLlower : -(1 : ℝ) / t ^ 2 ≤ -(upperTailSlope h t * (h + upperTailSlope h t)) := by
    simpa only [neg_div, neg_neg] using neg_le_neg hLbound
  have hRd := (((hL.const_add (-2)).add hk).sub hratio).congr_of_eventuallyEq hnear
  refine ⟨hTpos t ht, (hTd t ht).differentiableAt, hRd.differentiableAt, ?_⟩
  rw [hRd.deriv]
  calc
    -(3 : ℝ) / t ^ 2 = -(1 : ℝ) / t ^ 2 + -(2 : ℝ) / t ^ 2 := by
      rw [← add_div]
      norm_num
    _ ≤ -(upperTailSlope h t * (h + upperTailSlope h t)) + k := add_le_add hLlower hklower
    _ ≤ _ := le_sub_iff_add_le.mpr (add_le_of_nonpos_right hratioNonpos)

/-- The midpoint estimate for the actual radical. The variance identity
supplies the curvature bound from the upper bound on the log slope. -/
theorem separatedFour_radical_root_dividedDifference_average {h d v : ℝ}
    (hh : 0 < h) (hd : 4 ≤ d) (hdv : d < v)
    (hupper : ∀ t ∈ Icc d v,
      deriv (deriv (upperTailRadicalRoot h)) t / deriv (upperTailRadicalRoot h) t ≤
        -(17 / 12 : ℝ)) :
    let z := upperTailRadicalRoot h
    let T := deriv z
    deriv T d / T d - (T v - T d) / (z v - z d) ≤ 3 * (v - d) / (d * (d + v)) := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  have hjet (t : ℝ) (ht : t ∈ Icc d v) :
      0 < T t ∧ DifferentiableAt ℝ T t ∧ DifferentiableAt ℝ (fun s ↦ deriv T s / T s) t ∧
        -(3 : ℝ) / t ^ 2 ≤ deriv (fun s ↦ deriv T s / T s) t :=
    radicalRoot_logSlope_curvature hh (by linarith [ht.1])
      ((hupper t ht).trans (by norm_num))
  have hz (t : ℝ) (ht : t ∈ Icc d v) : HasDerivAt z (T t) t :=
    (hasDerivAt_upperTailRadicalRoot hh (by linarith [ht.1] : 0 < t)).differentiableAt.hasDerivAt
  have hTcont : ContinuousOn T (Icc d v) :=
    fun t ht ↦ (hjet t ht).2.1.continuousAt.continuousWithinAt
  have hFTC : (∫ t in d..v, T t) = z v - z d :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hdv.le
      (fun t ht ↦ (hz t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ hz t (Ioo_subset_Icc_self ht)) (hTcont.intervalIntegrable_of_Icc hdv.le)
  change deriv T d / T d - (T v - T d) / (z v - z d) ≤ 3 * (v - d) / (d * (d + v))
  rw [← hFTC]
  exact separatedFour_radical_dividedDifference_average hd hdv
    (fun t ht ↦ (hjet t ht).1) (fun t ht ↦ (hjet t ht).2.1)
    (fun t ht ↦ (hjet t ht).2.2.1) hupper (fun t ht ↦ (hjet t ht).2.2.2)

end RefinedBMV.PositiveCenter
