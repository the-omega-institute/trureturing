/- GID: D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/NymanFractionalMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real fractional-part Mellin identity at the actual Riemann zeta function. -/

/-
Source port: jrgochan/prime, commit ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2.
Copyright 2026 Jason Robert Gochanour. Licensed under Apache-2.0.
The complete upstream license is retained in NymanMellinHelpers.lean.
Modified by trureturing, 2026-09-08: trimmed imports and unused declarations,
routed namespaces, current-pin API adaptation, exact prerequisite reuse,
and the real-parameter scaling companion from BDMellin.lean:169-363.
Retirement: when this repository's installed future mathlib pin contains an
equivalent declaration, use it directly in new content; any frozen port remains
subject to the repository's frozen-content migration rules.
-/

import D5.S3.Weil.ZetaPntBounds.NymanMellinFloorSeries
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Complex Real MeasureTheory Set Filter Asymptotics TopologicalSpace Topology
open D5.S3.Weil.ZetaPntBounds.NymanMellinHelpers D5.S3.Weil.ZetaPntBounds.NymanMellinFloorSeries
namespace D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

/-- The function {1/x} · 1_{(0,1]}(x), extended by zero to all of ℝ.
    This is the integrand's "coefficient" for the Mellin transform. -/
private def fractInvIoc (x : ℝ) : ℂ :=
  indicator (Ioc 0 1) (fun t => ((Int.fract (1 / t) : ℝ) : ℂ)) x

/-- fractInvIoc is bounded by 1 everywhere. -/
private lemma fractInvIoc_norm_le (x : ℝ) : ‖fractInvIoc x‖ ≤ 1 := by
  unfold fractInvIoc
  by_cases hx : x ∈ Ioc 0 1
  · simp [indicator_of_mem hx, Complex.norm_real]
    exact (abs_of_nonneg (Int.fract_nonneg _)).le.trans (Int.fract_lt_one _).le
  · simp [indicator_of_notMem hx]

/-- fractInvIoc vanishes on (1, ∞). -/
private lemma fractInvIoc_eq_zero_of_gt_one {x : ℝ} (hx : 1 < x) : fractInvIoc x = 0 := by
  unfold fractInvIoc
  exact indicator_of_notMem (fun h => not_le.mpr hx h.2) _

/-- fractInvIoc is O(x^(-0)) = O(1) near 0. -/
private lemma fractInvIoc_isBigO_zero :
    fractInvIoc =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  simp only [neg_zero, rpow_zero]
  exact isBigO_of_le _ (fun x => by simp [fractInvIoc_norm_le x])

/-- fractInvIoc is O(x^(-a)) at ∞ for any a (it vanishes for x > 1). -/
private lemma fractInvIoc_isBigO_top (a : ℝ) :
    fractInvIoc =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [one_mul, fractInvIoc_eq_zero_of_gt_one (by linarith), norm_zero]
  exact norm_nonneg _

/-- fractInvIoc is measurable. -/
private lemma fractInvIoc_aestronglyMeasurable :
    AEStronglyMeasurable fractInvIoc (volume : Measure ℝ) := by
  unfold fractInvIoc
  exact (Measurable.indicator
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_const.div measurable_id).fract))
    measurableSet_Ioc).aestronglyMeasurable

/-- fractInvIoc is globally integrable (bounded on finite-measure support). -/
private lemma fractInvIoc_integrable : Integrable fractInvIoc (volume : Measure ℝ) := by
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ioc (0:ℝ) 1)
  · apply Measure.integrableOn_of_bounded (show volume (Ioc (0:ℝ) 1) ≠ ⊤ from measure_Ioc_lt_top.ne)
    · exact fractInvIoc_aestronglyMeasurable
    · filter_upwards with x
      unfold fractInvIoc
      by_cases hx : x ∈ Ioc (0:ℝ) 1
      · simp [indicator_of_mem hx, Complex.norm_real]
        exact (abs_of_nonneg (Int.fract_nonneg _)).le.trans (Int.fract_lt_one _).le
      · simp [indicator_of_notMem hx]
  · intro x hx; unfold fractInvIoc; exact indicator_of_notMem hx _

/-- fractInvIoc is locally integrable on (0, ∞). -/
private lemma fractInvIoc_locallyIntegrableOn :
    LocallyIntegrableOn fractInvIoc (Ioi 0) :=
  fractInvIoc_integrable.locallyIntegrable.locallyIntegrableOn (Ioi 0)

/-- The LHS integral over Ioo equals the integral over Ioc (measure-zero difference). -/
private lemma integral_Ioo_eq_Ioc (s : ℂ) :
    ∫ x in Ioo (0:ℝ) 1, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)  =
    ∫ x in Ioc (0:ℝ) 1, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)  :=
  (integral_Ioc_eq_integral_Ioo).symm

/-- The LHS integral equals the Mellin transform of fractInvIoc. -/
private lemma lhs_eq_mellin (s : ℂ) :
    ∫ x in Ioo (0:ℝ) 1, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
    mellin fractInvIoc s := by
  rw [integral_Ioo_eq_Ioc]
  have h_comm : ∀ x : ℝ, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * ((Int.fract (1 / x) : ℝ) : ℂ) := fun x => mul_comm _ _
  simp_rw [h_comm]
  unfold mellin
  simp only [smul_eq_mul]
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * ((Int.fract (1 / t) : ℝ) : ℂ)
  show ∫ x in Ioc (0:ℝ) 1, g x = ∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1) * fractInvIoc x
  have h_key : (fun x : ℝ => (x:ℂ)^(s-1) * fractInvIoc x) = indicator (Ioc (0:ℝ) 1) g := by
    ext x; unfold fractInvIoc g
    by_cases hx : x ∈ Ioc (0:ℝ) 1
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, mul_zero]
  rw [h_key, setIntegral_indicator measurableSet_Ioc]
  show ∫ x in Ioc (0:ℝ) 1, g x = ∫ x in Ioi (0:ℝ) ∩ Ioc (0:ℝ) 1, g x
  rw [inter_eq_right.mpr Ioc_subset_Ioi_self]

/-- The LHS is differentiable at every s with Re(s) > 0. -/
private lemma lhs_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin fractInvIoc) s :=
  mellin_differentiableAt_of_isBigO_rpow fractInvIoc_locallyIntegrableOn
    (fractInvIoc_isBigO_top (s.re + 1)) (by linarith)
    fractInvIoc_isBigO_zero (by linarith : (0 : ℝ) < s.re)

/-- The domain {Re > 0} \ {1} is open. -/
private lemma domain_isOpen :
    IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

/-- The LHS is analytic on {Re(s) > 0} \ {1}. -/
private lemma lhs_analyticOnNhd :
    AnalyticOnNhd ℂ (mellin fractInvIoc) {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
  (DifferentiableOn.analyticOnNhd
    (fun _s hs => (lhs_differentiableAt hs.1).differentiableWithinAt) domain_isOpen)

-- ════════════════════════════════════════════════════
-- Section 2: The RHS analyticity
-- ════════════════════════════════════════════════════

/-- The RHS function: s ↦ 1/(s-1) - ζ(s)/s. -/
private def rhs (s : ℂ) : ℂ := 1 / (s - 1) - riemannZeta s / s

/-- The RHS is differentiable on {Re(s) > 0} \ {1}. -/
private lemma rhs_differentiableOn :
    DifferentiableOn ℂ rhs {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s ⟨hs_pos, hs_ne⟩
  have hs_ne_zero : s ≠ 0 := by intro h; rw [h, zero_re] at hs_pos; linarith
  have h_sub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne
  unfold rhs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.sub
  · exact (differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ))) h_sub_ne
  · exact (differentiableAt_riemannZeta hs_ne).div differentiableAt_id hs_ne_zero

/-- The RHS is analytic on {Re(s) > 0} \ {1}. -/
private lemma rhs_analyticOnNhd :
    AnalyticOnNhd ℂ rhs {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
  rhs_differentiableOn.analyticOnNhd domain_isOpen

-- ════════════════════════════════════════════════════
-- Section 3: Agreement for Re(s) > 1
-- ════════════════════════════════════════════════════

/-- For Re(s) > 1, the fract integral equals 1/(s-1) - ζ(s)/s.
    Uses FloorDivMellin.lean: mellin_fractBasis with k=1. -/
private lemma lhs_eq_rhs_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    mellin fractInvIoc s = rhs s := by
  -- Step 1: Unfold mellin fractInvIoc to ∫ Ioc, matching mellinRestricted
  rw [← lhs_eq_mellin s, integral_Ioo_eq_Ioc]
  -- Step 2: Commute factors to match mellinRestricted form
  simp_rw [show ∀ x : ℝ, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * ((Int.fract (1 / x) : ℝ) : ℂ) from fun x => mul_comm _ _]
  -- Step 3: This IS mellinRestricted (fractBasisC 1) s
  have h_mellin := mellin_fractBasis 1 (by omega) s hs
  unfold mellinRestricted fractBasisC at h_mellin
  -- Step 4: Cast alignment: Nat.cast 1 / x = 1 / x
  have h_cast : ∀ x : ℝ, Int.fract ((1 : ℕ) / x) = Int.fract (1 / x) := by
    intro x; norm_num
  simp_rw [h_cast] at h_mellin
  rw [h_mellin]
  -- Step 5: Algebraic simplification
  unfold rhs
  have hs_ne : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1_ne : s - 1 ≠ 0 := by intro h; have := congr_arg re h; simp [sub_re, one_re] at this; linarith
  have h_sum : (Finset.range 1).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))) = 1 := by
    simp [one_cpow]
  rw [h_sum]; simp only [Nat.cast_one, one_cpow]
  field_simp; ring

-- ════════════════════════════════════════════════════
-- Section 4: The Identity Theorem
-- ════════════════════════════════════════════════════

/-- Connectedness reused from the repository's zeta continuation domain. -/
private lemma domain_isPreconnected :
    IsPreconnected {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
  by simpa only [and_comm] using isPathConnected_aux.isConnected.isPreconnected

/-- 2 belongs to the domain. -/
private lemma two_mem_domain : (2 : ℂ) ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  refine ⟨?_, ?_⟩
  · show 0 < (2 : ℂ).re; norm_num
  · intro h; have := congr_arg Complex.re h; norm_num at this

/-- The main technical lemma: LHS agrees with RHS on all of {Re > 0} \ {1}. -/
private lemma mellin_fractInvIoc_eq_rhs :
    EqOn (mellin fractInvIoc) rhs {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    lhs_analyticOnNhd rhs_analyticOnNhd domain_isPreconnected two_mem_domain
  apply Filter.eventually_of_mem
    (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re from by norm_num))
  exact fun s hs => lhs_eq_rhs_of_re_gt_one hs

-- ════════════════════════════════════════════════════
-- Section 5: The selected upstream base identity
-- ════════════════════════════════════════════════════

/-- The fractional-part Mellin base identity from IdentityBypass.lean:220:
    ∫₀¹ {1/x} · x^{s-1} dx = 1/(s-1) - ζ(s)/s for Re(s) > 0, s ≠ 1. -/
theorem bd_mellin_base_case_proved (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∫ x in Ioo (0:ℝ) 1, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
    1 / (s - 1) - riemannZeta s / s := by
  rw [lhs_eq_mellin]
  exact mellin_fractInvIoc_eq_rhs ⟨hs, hs1⟩

private lemma fractionalMellin_integrableOn_Ioc (theta b : ℝ) (hb : 0 ≤ b)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract (theta / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc 0 b) := by
  have hp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc 0 b) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    apply intervalIntegral.intervalIntegrable_cpow'
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  refine Integrable.mono hp ?_ ?_
  · exact ((Complex.continuous_ofReal.measurable.comp
      (measurable_const.div measurable_id).fract).aestronglyMeasurable.restrict).mul
        hp.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg (theta / x))]
      using (Int.fract_lt_one (theta / x)).le

/-- The bounded fractional part is Mellin integrable for every real parameter. -/
theorem fractionalMellin_integrableOn (theta : ℝ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract (theta / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioo 0 1) :=
  (fractionalMellin_integrableOn_Ioc theta 1 (by norm_num) s hs).mono_set
    Ioo_subset_Ioc_self

-- Adapted from BDMellin.lean:169-363 at the immutable source commit above.
-- The scale is real; no continuity of the fractional part is used.
private theorem mellin_substitution_real (k : ℝ) (hk : 0 < k) (s : ℂ) :
    (∫ x in Ioo (0 : ℝ) 1, ((Int.fract (1 / (k * x)) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
    (k : ℂ) ^ (-s) *
      ∫ u in Ioo (0 : ℝ) k, ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) := by
  have hk_ne := ne_of_gt hk
  have hk_c_ne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_ne
  let g : ℝ → ℂ := fun u => ((Int.fract (1 / u) : ℝ) : ℂ) * ((u / k : ℝ) : ℂ) ^ (s - 1)
  have h_eq_lhs : ∀ x ∈ uIcc (0 : ℝ) 1,
      g (x * k) = ((Int.fract (1 / (k * x)) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    intro x _
    dsimp [g]
    rw [mul_div_cancel_right₀ x hk_ne, mul_comm x k]
  have h_expand : ∀ u ∈ uIcc (0 : ℝ) k,
      g u = ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) *
        (k : ℂ) ^ (-(s - 1)) := by
    intro u hu
    rw [uIcc_of_le hk.le] at hu
    dsimp [g]
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hu.1 hk.le, cpow_neg]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le hk.le]
  rw [← intervalIntegral.integral_congr h_eq_lhs,
    intervalIntegral.integral_comp_mul_right (f := g) hk_ne]
  simp only [zero_mul, one_mul]
  rw [intervalIntegral.integral_congr h_expand, intervalIntegral.integral_mul_const,
    Complex.real_smul, Complex.ofReal_inv, ← cpow_neg_one (k : ℂ)]
  rw [← mul_assoc, mul_right_comm, ← cpow_add _ _ hk_c_ne]
  congr 2
  ring

private theorem mellin_integral_split_real (k : ℝ) (hk : 1 ≤ k)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ u in Ioo (0 : ℝ) k, ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) =
    (∫ u in Ioo (0 : ℝ) 1, ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) +
    ∫ u in Ioo (1 : ℝ) k, ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have h0 := fractionalMellin_integrableOn_Ioc 1 1 (by norm_num) s hs
  have h1 := (fractionalMellin_integrableOn_Ioc 1 k hk0 s hs).mono_set
    (show Ioc 1 k ⊆ Ioc 0 k from fun _ h => ⟨lt_trans (by norm_num) h.1, h.2⟩)
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hk0,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le hk]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr h0)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hk).mpr h1)).symm

private theorem mellin_tail_real (k : ℝ) (hk : 1 ≤ k) (s : ℂ) (hs1 : s ≠ 1) :
    (∫ u in Ioo (1 : ℝ) k, ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) =
    ((k : ℂ) ^ (s - 1) - 1) / (s - 1) := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have heq : EqOn
      (fun u : ℝ => ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
      (fun u : ℝ => (u : ℂ) ^ (s - 2)) (Ioc 1 k) := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by norm_num) hu.1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    have hf : Int.fract (1 / u) = 1 / u :=
      Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hu0).mpr hu.1⟩
    dsimp only
    rw [hf, one_div, Complex.ofReal_inv,
      show (s - 2 : ℂ) = -1 + (s - 1) from by ring,
      cpow_add (-1) (s - 1) hu_ne, cpow_neg_one]
  rw [setIntegral_congr_fun measurableSet_Ioc heq,
    ← intervalIntegral.integral_of_le hk]
  have hne : s - 2 ≠ -1 := by intro h; apply hs1; linear_combination h
  rw [integral_cpow (Or.inr ⟨hne, fun h => by
    rw [uIcc_of_le hk] at h; linarith [h.1]⟩)]
  rw [show s - 2 + 1 = s - 1 from by ring, Complex.ofReal_one, one_cpow]

/-- Real-parameter scaling, including the degenerate tail at theta = 1. -/
theorem fractionalMellin_scaling (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioo (0 : ℝ) 1, ((Int.fract (theta / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
    (theta : ℂ) ^ s *
      (∫ x in Ioo (0 : ℝ) 1, ((Int.fract (1 / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) +
    ((theta : ℂ) - (theta : ℂ) ^ s) / (s - 1) := by
  have hk : 1 ≤ theta⁻¹ := (one_le_inv₀ htheta).mpr htheta1
  have hp : ((theta⁻¹ : ℝ) : ℂ) ^ (-s) = (theta : ℂ) ^ s := by
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg htheta.le, cpow_neg, inv_inv]
  have harg : ∀ x : ℝ, theta / x = 1 / (theta⁻¹ * x) := by
    intro x; simp [div_eq_mul_inv, mul_comm]
  simp_rw [harg]
  rw [mellin_substitution_real theta⁻¹ (inv_pos.mpr htheta) s,
    mellin_integral_split_real theta⁻¹ hk s hs, mul_add, mellin_tail_real theta⁻¹ hk s hs1]
  have ht_ne : ((theta⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_ne_zero htheta.ne')
  have hprod : ((theta⁻¹ : ℝ) : ℂ) ^ (-s) *
      ((theta⁻¹ : ℝ) : ℂ) ^ (s - 1) = (theta : ℂ) := by
    rw [← cpow_add _ _ ht_ne, show -s + (s - 1) = (-1 : ℂ) from by ring,
      cpow_neg_one, Complex.ofReal_inv, inv_inv]
  rw [mul_div_assoc', mul_sub, hprod, mul_one, hp]

/-- E9: the literal fractional-part integral for every source-allowed real theta. -/
theorem fractionalMellin_eq_zeta (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (hs_lt : s.re < 1) :
    (∫ x in Ioo (0 : ℝ) 1, ((Int.fract (theta / x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
    (theta : ℂ) / (s - 1) - (theta : ℂ) ^ s * riemannZeta s / s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs_lt
  rw [fractionalMellin_scaling theta htheta htheta1 s hs hs1,
    bd_mellin_base_case_proved s hs hs1]
  ring

end D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
