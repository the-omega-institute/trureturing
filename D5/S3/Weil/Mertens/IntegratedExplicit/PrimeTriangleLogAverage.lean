/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage
   mirror-E: none(waiver:prime-triangle-log-window)
   anchors: []
   utility: none
   digest: A unit logarithmic window bound for the centered ordinary-prime triangle characterizes RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleSquareLimit
import D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

/-! A unit logarithmic window criterion for the centered ordinary-prime triangle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLogAverage

open Filter MeasureTheory Set
open scoped Topology BigOperators
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open PrimeQuarterTriangle (hinge mangoldtHingeSum primeTriangleSum triangleWeight)
open PrimeTriangleSquareLimit (normalized_mangoldtHinge_sub_primeTriangle_tendsto)
open SignedPrimePrimitiveCriterion
  (rh_iff_signedPrimePrimitive_affine_bounds_from_5040)
open PrimeOnlyTailCorrection (primeTail)
open RobinWeightedZeroLaplace (firstLiMass_lt_twentieth)

open private hinge_mangoldtRamp_eq upper_bound_of_hinge_lower_bound
  tendsto_mangoldtRamp_div primeTriangleSum_eq_prefix from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

open private cutoff completeDensity completeDensity_continuous completePrimitive
  completePrimitive_continuous primitive_prime_power_bound signedPrimePrimitive_eq_from_5040
  normalizedActualZeroSeries normalizedActualZeroSeries_continuous
  normalizedActualZeroSeries_window_bound from
  D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

private def unitWindow (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in t..t + 1, f u

private def normalizedMangoldt (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (mangoldtHingeSum (Real.exp t) - 2 * Real.exp t * Real.log 2)

private def squareBias : ℝ := 6 * Real.sqrt 2 - 8

private def normalizedPrime (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (primeTriangleSum (Real.exp t) - 2 * Real.exp t * Real.log 2) +
    squareBias

private def dyadicCombination (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * f (t + 2 * cutoff) - 3 * Real.sqrt 2 * f (t + cutoff) + 2 * f t

private lemma exp_neg_half_eq_inv_sqrt (t : ℝ) :
    Real.exp (-t / 2) = (Real.sqrt (Real.exp t))⁻¹ := by
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg, Real.exp_half]

private lemma sqrt_mul_normalized_shift (v : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.sqrt a * (Real.exp (-(t + Real.log a) / 2) * v (Real.exp (t + Real.log a))) =
      Real.exp (-t / 2) * v (a * Real.exp t) := by
  have he : Real.exp (t + Real.log a) = a * Real.exp t := by
    rw [Real.exp_add, Real.exp_log ha, mul_comm]
  simp only [exp_neg_half_eq_inv_sqrt, he, Real.sqrt_mul ha.le, mul_inv]
  calc
    _ = (Real.sqrt a * (Real.sqrt a)⁻¹) *
        ((Real.sqrt (Real.exp t))⁻¹ * v (a * Real.exp t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_mul]

private lemma normalized_hinge_eq (v : ℝ → ℝ) (t : ℝ) :
    Real.exp (-t / 2) * hinge v (Real.exp t) =
      dyadicCombination (fun u => Real.exp (-u / 2) * v (Real.exp u)) t := by
  have hlog4 : Real.log 4 = 2 * cutoff := by
    rw [cutoff, show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have h4 := sqrt_mul_normalized_shift v (by norm_num : (0 : ℝ) < 4) t
  have h2 := sqrt_mul_normalized_shift v (by norm_num : (0 : ℝ) < 2) t
  rw [hlog4, show Real.sqrt 4 = (2 : ℝ) by norm_num] at h4
  change Real.sqrt 2 * (Real.exp (-(t + cutoff) / 2) * v (Real.exp (t + cutoff))) =
    Real.exp (-t / 2) * v (2 * Real.exp t) at h2
  dsimp only [dyadicCombination, hinge]
  linarith only [h2, h4]

private lemma normalizedMangoldt_eq (t : ℝ) :
    normalizedMangoldt t = dyadicCombination completeDensity t := by
  unfold normalizedMangoldt
  rw [← hinge_mangoldtRamp_eq (Real.exp_pos t), normalized_hinge_eq]
  rfl

private lemma unitWindow_dyadicCombination {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    unitWindow (dyadicCombination f) t = dyadicCombination (unitWindow f) t := by
  have hshift (d : ℝ) : Continuous (fun u => f (u + d)) :=
    hf.comp (continuous_id.add continuous_const)
  have hleft := ((hshift (2 * cutoff)).const_mul 2).intervalIntegrable (μ := volume) t (t + 1)
  have hmiddle :=
    ((hshift cutoff).const_mul (3 * Real.sqrt 2)).intervalIntegrable (μ := volume) t (t + 1)
  have hright := (hf.const_mul 2).intervalIntegrable (μ := volume) t (t + 1)
  have htranslate (d : ℝ) : (∫ u in t..t + 1, f (u + d)) = unitWindow f (t + d) := by
    rw [intervalIntegral.integral_comp_add_right, unitWindow]
    rw [show t + 1 + d = t + d + 1 by ring]
  simp only [unitWindow] at htranslate
  simp only [unitWindow, dyadicCombination]
  rw [intervalIntegral.integral_add (hleft.sub hmiddle) hright,
    intervalIntegral.integral_sub hleft hmiddle]
  simp only [intervalIntegral.integral_const_mul, htranslate]

private lemma mangoldt_window_eq (t : ℝ) :
    unitWindow normalizedMangoldt t = dyadicCombination (unitWindow completeDensity) t := by
  have h : normalizedMangoldt = dyadicCombination completeDensity := funext normalizedMangoldt_eq
  rw [h, unitWindow_dyadicCombination completeDensity_continuous]

-- On a bounded x-interval, the extra terms in a fixed prime prefix vanish.
private lemma prime_triangle_eq_fixed_sum {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : ⌊4 * x⌋₊ ≤ N) :
    primeTriangleSum x =
      ∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log n * triangleWeight x n := by
  rw [primeTriangleSum_eq_prefix hx]
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hp⟩
    rcases Finset.mem_Ioc.mp hn with ⟨hn0, hnN⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, hnN.trans hN⟩, hp⟩
  · intro n hn hnot
    rcases Finset.mem_filter.mp hn with ⟨hn, hp⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hcut : ⌊4 * x⌋₊ < n := by
      by_contra! h
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, h⟩, hp⟩)
    have hn4 : 4 * x < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hcut
    have h4 : 4 * x / (n : ℝ) - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ hn0).mpr (by simpa using hn4.le))
    have h2 : 2 * x / (n : ℝ) - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ hn0).mpr (by linarith only [hx, hn4]))
    have h1 : x / (n : ℝ) - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ hn0).mpr (by linarith only [hx, hn4]))
    simp [triangleWeight, max_eq_right h4, max_eq_right h2, max_eq_right h1]

private lemma prime_triangle_continuousAt {x : ℝ} (hx : 0 < x) :
    ContinuousAt primeTriangleSum x := by
  let N := ⌊4 * (x + 1)⌋₊
  let f : ℝ → ℝ := fun y =>
    ∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log n * triangleWeight y n
  have hf : Continuous f := by
    change Continuous (fun y : ℝ =>
      ∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log n * triangleWeight y n)
    apply continuous_finsetSum
    intro n _
    unfold triangleWeight
    fun_prop
  refine hf.continuousAt.congr ?_
  filter_upwards [Ioo_mem_nhds hx (by linarith : x < x + 1)] with y hy
  exact (prime_triangle_eq_fixed_sum hy.1.le
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hy.2.le (by norm_num)))).symm

private lemma normalizedPrime_continuous : Continuous normalizedPrime := by
  have hp : Continuous (fun t => primeTriangleSum (Real.exp t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (prime_triangle_continuousAt (Real.exp_pos t)).comp Real.continuous_exp.continuousAt
  unfold normalizedPrime
  fun_prop

private lemma normalizedMangoldt_continuous : Continuous normalizedMangoldt := by
  have h : normalizedMangoldt = dyadicCombination completeDensity := funext normalizedMangoldt_eq
  rw [h]
  have hg := completeDensity_continuous
  unfold dyadicCombination
  fun_prop

private lemma normalized_difference_tendsto :
    Tendsto (fun t => normalizedMangoldt t - normalizedPrime t) atTop (𝓝 0) := by
  have hc := normalized_mangoldtHinge_sub_primeTriangle_tendsto.comp Real.tendsto_exp_atTop
  have hh : Tendsto (fun t =>
      (mangoldtHingeSum (Real.exp t) - primeTriangleSum (Real.exp t)) /
        Real.sqrt (Real.exp t) - squareBias) atTop (𝓝 0) := by
    change Tendsto (fun t =>
      (mangoldtHingeSum (Real.exp t) - primeTriangleSum (Real.exp t)) /
        Real.sqrt (Real.exp t)) atTop (𝓝 squareBias) at hc
    simpa only [sub_self] using hc.sub (tendsto_const_nhds (x := squareBias))
  apply hh.congr'
  filter_upwards with t
  simp only [normalizedMangoldt, normalizedPrime, exp_neg_half_eq_inv_sqrt]
  rw [div_eq_inv_mul]
  ring

private lemma unitWindow_norm_le {f : ℝ → ℝ} {t C : ℝ}
    (h : ∀ u ∈ Icc t (t + 1), ‖f u‖ ≤ C) : ‖unitWindow f t‖ ≤ C := by
  unfold unitWindow
  have ht : t ≤ t + 1 := by linarith
  calc
    ‖∫ u in t..t + 1, f u‖ ≤ C * |(t + 1) - t| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu =>
        h u (by simpa only [uIcc_of_le ht] using uIoc_subset_uIcc hu))
    _ = C := by rw [show t + 1 - t = 1 by ring, abs_one, mul_one]

private lemma eventually_unitWindow_norm_le {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ‖unitWindow f t‖ ≤ ε := by
  rw [NormedAddGroup.tendsto_nhds_zero] at hf
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hf ε hε)
  filter_upwards [eventually_ge_atTop T] with t ht
  exact unitWindow_norm_le (fun u hu => (hT u (ht.trans hu.1)).le)

private lemma eventually_window_difference_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, |unitWindow normalizedMangoldt t - unitWindow normalizedPrime t| ≤ ε := by
  filter_upwards [eventually_unitWindow_norm_le normalized_difference_tendsto hε] with t ht
  simpa only [unitWindow, Real.norm_eq_abs,
    intervalIntegral.integral_sub (normalizedMangoldt_continuous.intervalIntegrable (μ := volume) t (t + 1))
      (normalizedPrime_continuous.intervalIntegrable (μ := volume) t (t + 1))] using ht

private lemma zero_series_window_bound (hRH : RiemannHypothesis) (t : ℝ) :
    ‖unitWindow (fun u => (normalizedActualZeroSeries u).re) t‖ ≤ 1 / 100 := by
  have ht : t ≤ t + 1 := by linarith
  have hre : unitWindow (fun u => (normalizedActualZeroSeries u).re) t =
      (∫ u in t..t + 1, normalizedActualZeroSeries u).re := by
    rw [unitWindow, intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    exact integral_re (normalizedActualZeroSeries_continuous.intervalIntegrable _ _).1
  have h := normalizedActualZeroSeries_window_bound hRH t (t + 1)
  rw [(RHSharpActualEnvelope.coeff_norm_hasSum hRH).tsum_eq] at h
  rw [hre, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (h.trans (by linarith [firstLiMass_lt_twentieth]))

private lemma eventually_ramp_window_bound (hRH : RiemannHypothesis) :
    ∀ᶠ t in atTop, |unitWindow completeDensity t| ≤ (1001 / 100000 : ℝ) := by
  let s : ℝ → ℝ := fun u => (normalizedActualZeroSeries u).re
  have hs : Continuous s := Complex.continuous_re.comp normalizedActualZeroSeries_continuous
  have hrem : Tendsto (fun u => completeDensity u - s u) atTop (𝓝 0) := by
    simpa only [completeDensity, RHSharpActualEnvelope.G, s, normalizedActualZeroSeries,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      RHSharpActualEnvelope.G_sub_normalized_actualH_tendsto_zero
  filter_upwards [eventually_unitWindow_norm_le hrem (by norm_num : (0 : ℝ) < 1 / 100000)]
    with t ht
  have hs' : ‖unitWindow s t‖ ≤ 1 / 100 := zero_series_window_bound hRH t
  have he : unitWindow completeDensity t =
      unitWindow (fun u => completeDensity u - s u) t + unitWindow s t := by
    simp only [unitWindow, intervalIntegral.integral_sub
      (completeDensity_continuous.intervalIntegrable (μ := volume) t (t + 1))
      (hs.intervalIntegrable (μ := volume) t (t + 1)),
      sub_add_cancel]
  rw [← Real.norm_eq_abs, he]
  exact (norm_add_le _ _).trans (by linarith only [ht, hs'])

private lemma dyadicCombination_abs_le {f : ℝ → ℝ} {t C : ℝ} (hC : 0 ≤ C)
    (h0 : |f t| ≤ C) (h1 : |f (t + cutoff)| ≤ C) (h2 : |f (t + 2 * cutoff)| ≤ C) :
    |dyadicCombination f t| ≤ (577 / 70 : ℝ) * C := by
  have hroot : Real.sqrt 2 ≤ (99 / 70 : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrootC := mul_le_mul_of_nonneg_right hroot hC
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp h1).1 (Real.sqrt_nonneg 2)
  have hu := mul_le_mul_of_nonneg_left (abs_le.mp h1).2 (Real.sqrt_nonneg 2)
  rw [abs_le] at h0 h2 ⊢
  unfold dyadicCombination
  constructor <;> linarith only [hrootC, hl, hu, h0.1, h0.2, h2.1, h2.2]

private lemma prime_window_lower_of_rh (hRH : RiemannHypothesis) :
    ∀ᶠ t in atTop, -(1 / 12 : ℝ) ≤ unitWindow normalizedPrime t := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_ramp_window_bound hRH)
  have hh : 0 ≤ cutoff := Real.log_nonneg (by norm_num)
  filter_upwards [eventually_ge_atTop T,
    eventually_window_difference_le (by norm_num : (0 : ℝ) < 1 / 10000)] with t ht he
  have hm : |unitWindow normalizedMangoldt t| ≤ (577 / 70 : ℝ) * (1001 / 100000) := by
    rw [mangoldt_window_eq t]
    exact dyadicCombination_abs_le (by norm_num) (hT t ht)
      (hT _ (by linarith only [ht, hh])) (hT _ (by linarith only [ht, hh]))
  linarith only [(abs_le.mp hm).1, (abs_le.mp he).2]

private def smoothedRamp (x : ℝ) : ℝ :=
  Real.sqrt x * unitWindow completeDensity (Real.log x)

private lemma normalized_smoothedRamp (t : ℝ) :
    Real.exp (-t / 2) * smoothedRamp (Real.exp t) = unitWindow completeDensity t := by
  rw [smoothedRamp, Real.log_exp, exp_neg_half_eq_inv_sqrt, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (Real.exp_pos t)).ne', one_mul]

private lemma smoothed_hinge_eq (t : ℝ) :
    Real.exp (-t / 2) * hinge smoothedRamp (Real.exp t) = unitWindow normalizedMangoldt t := by
  have h : (fun u => Real.exp (-u / 2) * smoothedRamp (Real.exp u)) =
      unitWindow completeDensity := funext normalized_smoothedRamp
  rw [normalized_hinge_eq, h, mangoldt_window_eq]

private lemma completePrimitive_step (t : ℝ) :
    completePrimitive (t + 1) - completePrimitive t = unitWindow completeDensity t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (completeDensity_continuous.intervalIntegrable (μ := volume) cutoff t)
    (completeDensity_continuous.intervalIntegrable (μ := volume) t (t + 1))
  change completePrimitive t + unitWindow completeDensity t = completePrimitive (t + 1) at h
  linarith only [h]

private lemma smoothedRamp_continuousOn {X : ℝ} (hX : 0 < X) :
    ContinuousOn smoothedRamp (Icc X (2 * X)) := by
  have he : unitWindow completeDensity = fun t =>
      completePrimitive (t + 1) - completePrimitive t :=
    funext fun t => (completePrimitive_step t).symm
  have hH : Continuous (unitWindow completeDensity) := by
    rw [he]
    have hF := completePrimitive_continuous
    fun_prop
  unfold smoothedRamp
  exact Real.continuous_sqrt.continuousOn.mul
    (hH.comp_continuousOn (Real.continuousOn_log.mono (fun _ hx => (hX.trans_le hx.1).ne')))

private lemma smoothedRamp_div_tendsto_zero :
    Tendsto (fun x => smoothedRamp x / x) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let E := Real.exp (1 / 2)
  have hE : 0 < E := Real.exp_pos _
  have hsmall : ∀ᶠ u : ℝ in atTop, ‖U (Real.exp u) / Real.exp u‖ < ε / (2 * E) :=
    (NormedAddGroup.tendsto_nhds_zero.mp (tendsto_mangoldtRamp_div.comp Real.tendsto_exp_atTop))
      _ (by positivity)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  have htend := Real.tendsto_log_atTop.eventually (eventually_ge_atTop T)
  filter_upwards [htend, eventually_gt_atTop (0 : ℝ)] with x hxT hx
  let t := Real.log x
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hvalue : smoothedRamp x / x = Real.exp (-t / 2) * unitWindow completeDensity t := by
    have hroot : Real.exp (-t / 2) = (Real.sqrt x)⁻¹ := by
      rw [exp_neg_half_eq_inv_sqrt, show Real.exp t = x from Real.exp_log hx]
    change Real.sqrt x * unitWindow completeDensity t / x = _
    rw [hroot]
    calc
      _ = Real.sqrt x * unitWindow completeDensity t / (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt hx.le]
      _ = _ := by field_simp [hs.ne']
  have hintegrand (u : ℝ) :
      Real.exp (-t / 2) * completeDensity u =
        Real.exp ((u - t) / 2) * (U (Real.exp u) / Real.exp u) := by
    rw [completeDensity, div_eq_inv_mul (U (Real.exp u)) (Real.exp u), ← Real.exp_neg]
    calc
      _ = Real.exp (-t / 2 + -u / 2) * U (Real.exp u) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp ((u - t) / 2 + -u) * U (Real.exp u) := by
        rw [show -t / 2 + -u / 2 = (u - t) / 2 + -u by ring]
      _ = _ := by rw [Real.exp_add, mul_assoc]
  have he : smoothedRamp x / x =
      unitWindow (fun u => Real.exp ((u - t) / 2) * (U (Real.exp u) / Real.exp u)) t := by
    rw [hvalue]
    change Real.exp (-t / 2) * (∫ u in t..t + 1, completeDensity u) =
      ∫ u in t..t + 1, Real.exp ((u - t) / 2) * (U (Real.exp u) / Real.exp u)
    rw [← intervalIntegral.integral_const_mul]
    simp only [hintegrand]
  rw [he]
  refine lt_of_le_of_lt (unitWindow_norm_le (C := ε / 2) ?_) (by linarith only [hε])
  intro u hu
  have ht : T ≤ t := hxT
  have hweight : Real.exp ((u - t) / 2) ≤ E := by
    exact Real.exp_le_exp.mpr (by linarith only [hu.2])
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ E * (ε / (2 * E)) :=
      mul_le_mul hweight (hT u (ht.trans hu.1)).le (norm_nonneg _) hE.le
    _ = ε / 2 := by field_simp [hE.ne']

private lemma ramp_window_upper_of_prime_window_lower
    (h : ∀ᶠ t in atTop, -(1 / 12 : ℝ) ≤ unitWindow normalizedPrime t) :
    ∃ C : ℝ, ∀ᶠ t in atTop, unitWindow completeDensity t ≤ C := by
  have hlower : ∀ᶠ t in atTop, -(1 : ℝ) ≤ unitWindow normalizedMangoldt t := by
    filter_upwards [h, eventually_window_difference_le (by norm_num : (0 : ℝ) < 1 / 12)]
      with t ht he
    linarith only [ht, (abs_le.mp he).1]
  have hlog := Real.tendsto_log_atTop.eventually hlower
  have hxLower : ∀ᶠ x : ℝ in atTop, -(1 : ℝ) * x ^ (1 / 2 : ℝ) ≤ hinge smoothedRamp x := by
    filter_upwards [hlog, eventually_gt_atTop (0 : ℝ)] with x hn hx
    change -(1 : ℝ) ≤ unitWindow normalizedMangoldt (Real.log x) at hn
    rw [← smoothed_hinge_eq, Real.exp_log hx] at hn
    rw [exp_neg_half_eq_inv_sqrt, Real.exp_log hx, ← div_eq_inv_mul] at hn
    rw [← Real.sqrt_eq_rpow]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr hx)).mp hn
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hxLower
  let X := max Y 1
  have hX : 0 < X := zero_lt_one.trans_le (le_max_right _ _)
  have hhinge : ∀ x ≥ X, -(1 : ℝ) * x ^ (1 / 2 : ℝ) ≤ hinge smoothedRamp x :=
    fun x hx => hY x ((le_max_left _ _).trans hx)
  obtain ⟨B, hB⟩ := upper_bound_of_hinge_lower_bound hX
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1) (smoothedRamp_continuousOn hX)
    smoothedRamp_div_tendsto_zero hhinge
  let D : ℝ := 1 / (((2 : ℝ) ^ (1 / 2 : ℝ) - 1) * (2 - (2 : ℝ) ^ (1 / 2 : ℝ)))
  refine ⟨|B| + D, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop X)] with t ht
  change X ≤ Real.exp t at ht
  have hroot : 1 ≤ Real.sqrt (Real.exp t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((le_max_right Y 1).trans ht)
  have hv := hB (Real.exp t) ht
  change smoothedRamp (Real.exp t) ≤ B + D * (Real.exp t) ^ (1 / 2 : ℝ) at hv
  rw [smoothedRamp, Real.log_exp, ← Real.sqrt_eq_rpow] at hv
  have hb : B ≤ |B| * Real.sqrt (Real.exp t) :=
    (le_abs_self B).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hroot (abs_nonneg B))
  apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (Real.exp_pos t))).mp
  linarith only [hv, hb]

private lemma completePrimitive_affine_upper {C : ℝ}
    (h : ∀ᶠ t in atTop, unitWindow completeDensity t ≤ C) :
    ∃ A B : ℝ, ∀ᶠ t in atTop, completePrimitive t ≤ A * t + B := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  let A := max C 0
  have hA : 0 ≤ A := le_max_right _ _
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show T ≤ T + 1 by linarith)) completePrimitive_continuous.continuousOn
  refine ⟨A, completePrimitive s₀ - A * T, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  let n : ℕ := ⌊t - T⌋₊
  let s := t - (n : ℝ)
  have hn : (n : ℝ) ≤ t - T := Nat.floor_le (sub_nonneg.mpr ht)
  have hnext : t - T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hs : s ∈ Icc T (T + 1) :=
    ⟨by dsimp [s]; linarith only [hn], by dsimp [s]; linarith only [hnext]⟩
  have htelescope (k : ℕ) : completePrimitive (s + k) ≤ completePrimitive s + A * k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : T ≤ s + (k : ℝ) := hs.1.trans (le_add_of_nonneg_right (Nat.cast_nonneg k))
      have hstep := completePrimitive_step (s + (k : ℝ))
      have hbound := (hT _ hk).trans (le_max_left C 0)
      rw [Nat.cast_succ, ← add_assoc]
      linarith only [ih, hstep, hbound]
  have he : s + (n : ℝ) = t := sub_add_cancel _ _
  have hlate := htelescope n
  rw [he] at hlate
  have hbase : completePrimitive s ≤ completePrimitive s₀ := hmax hs
  have hsize := mul_le_mul_of_nonneg_left hn hA
  linarith only [hlate, hbase, hsize]

private lemma rh_of_prime_window_lower
    (h : ∀ᶠ t in atTop, -(1 / 12 : ℝ) ≤ unitWindow normalizedPrime t) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ramp_window_upper_of_prime_window_lower h
  obtain ⟨A, B, hupper⟩ := completePrimitive_affine_upper hC
  obtain ⟨D, _, hgap⟩ := primitive_prime_power_bound
  let head : ℝ := ∫ x in 2..(5040 : ℝ), primeTail x / Real.sqrt x
  apply rh_iff_signedPrimePrimitive_affine_bounds_from_5040.2.mpr
  refine ⟨-A - D, -B - head, ?_⟩
  filter_upwards [hupper, eventually_ge_atTop cutoff, eventually_ge_atTop (Real.log 5040)]
    with t ht hcut hanchor
  have hcorr := hgap t hcut
  rw [Real.norm_eq_abs, abs_le, signedPrimePrimitive_eq_from_5040 hanchor] at hcorr
  change (-A - D) * t + (-B - head) ≤
    ∫ x in (5040 : ℝ)..Real.exp t, primeTail x / Real.sqrt x
  dsimp only [head]
  linarith only [ht, hcorr.1]

/-- RH is equivalent to the eventual lower bound on every unit log-window
of the ordinary-prime triangle centered by its main term and square bias. -/
theorem rh_iff_eventual_prime_triangle_log_average :
    RiemannHypothesis ↔ ∀ᶠ t : ℝ in atTop, -(1 / 12 : ℝ) ≤
      ∫ u in t..t + 1, (Real.exp (-u / 2) *
        (primeTriangleSum (Real.exp u) - 2 * Real.exp u * Real.log 2) + (6 * Real.sqrt 2 - 8)) :=
  ⟨prime_window_lower_of_rh, rh_of_prime_window_lower⟩

#print axioms rh_iff_eventual_prime_triangle_log_average

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLogAverage
