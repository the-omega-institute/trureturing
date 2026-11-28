/- GID: D5/S3/Weil/ZeroData/CanonicalLiZeroSum
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/CanonicalLiZeroSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The derivative-defined Li coefficients equal the absolutely convergent real zero sums. -/

import D5.S3.Weil.ZeroData.LiZeroSumConvergence
import D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
import D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reflection cancels the normalization constant in the xi resolvent.
The resulting rational kernels converge normally near the origin, so their
Taylor coefficients give the canonical Li coefficients without a zero-free
half-plane hypothesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZeroData.CanonicalLiZeroSum

open Complex Filter
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.LiZeroSumConvergence
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder

private def ratio (rho : ℂ) : ℂ := 1 - 1 / rho

private def kernel (Z : ZeroData) (k : ℕ) (z : ℂ) : ℂ :=
  (Z.multiplicity k : ℂ) / 2 *
    (2 * (1 - z)⁻¹ - ratio (Z.zero k) * (1 - ratio (Z.zero k) * z)⁻¹ -
      ratio (1 - Z.zero k) * (1 - ratio (1 - Z.zero k) * z)⁻¹)

private theorem zero_ne (Z : ZeroData) (k : ℕ) :
    Z.zero k ≠ 0 ∧ 1 - Z.zero k ≠ 0 := by
  have h := (Z.zero_isNontrivial k).2
  constructor
  · intro he
    rw [he] at h
    norm_num at h
  · intro he
    have he' : Z.zero k = 1 := (sub_eq_zero.mp he).symm
    rw [he'] at h
    norm_num at h

private theorem ratio_relations (rho : ℂ) (h0 : rho ≠ 0) (h1 : 1 - rho ≠ 0) :
    ratio rho * ratio (1 - rho) = 1 ∧
      ratio rho + ratio (1 - rho) = 2 - (rho * (1 - rho))⁻¹ := by
  dsimp [ratio]
  constructor <;> field_simp [h0, h1] <;> ring

private theorem denominator_identity (q r x z : ℂ)
    (hp : q * r = 1) (hs : q + r = 2 - x) :
    (1 - q * z) * (1 - r * z) = (1 - z) ^ 2 + x * z := by
  calc
    _ = 1 - (q + r) * z + (q * r) * z ^ 2 := by ring
    _ = _ := by rw [hp, hs]; ring

private theorem kernel_collapse (q r x z : ℂ)
    (hp : q * r = 1) (hs : q + r = 2 - x)
    (hz : 1 - z ≠ 0) (hd : (1 - z) ^ 2 + x * z ≠ 0) :
    2 * (1 - z)⁻¹ - q * (1 - q * z)⁻¹ - r * (1 - r * z)⁻¹ =
      x * (1 + z) / ((1 - z) * ((1 - z) ^ 2 + x * z)) := by
  have he := denominator_identity q r x z hp hs
  have hprod : (1 - q * z) * (1 - r * z) ≠ 0 := by rwa [he]
  have hq := (mul_ne_zero_iff.mp hprod).1
  have hr := (mul_ne_zero_iff.mp hprod).2
  rw [← he]
  field_simp [hz, hq, hr]
  linear_combination -(1 + z) * hs + 2 * z * hp

private theorem gamma_product (Z : ZeroData) (k : ℕ) :
    Z.zero k * (1 - Z.zero k) = (Z.gamma k) ^ 2 + 1 / 4 := by
  rw [Z.zero_eq_critical_add_I_mul_gamma]
  simp only [D5.S3.Weil.Convention.criticalAbscissa]
  ring_nf
  norm_num [Complex.I_sq]

private theorem inverse_product_bound (Z : ZeroData) (k : ℕ)
    (hk : 2 ≤ ‖Z.gamma k‖) :
    ‖(Z.zero k * (1 - Z.zero k))⁻¹‖ ≤ 1 / 2 ∧
      ‖(Z.zero k * (1 - Z.zero k))⁻¹‖ ≤
        2 / (1 + Complex.normSq (Z.gamma k)) := by
  let D := Z.zero k * (1 - Z.zero k)
  have hg : 4 ≤ ‖Z.gamma k‖ ^ 2 := by nlinarith [norm_nonneg (Z.gamma k)]
  have hd : ‖Z.gamma k‖ ^ 2 ≤ ‖D‖ + 1 / 4 := by
    calc
      _ = ‖(Z.gamma k) ^ 2‖ := (norm_pow _ _).symm
      _ = ‖D - 1 / 4‖ := by rw [show D = _ from gamma_product Z k]; congr 1; ring
      _ ≤ ‖D‖ + ‖(1 / 4 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by norm_num
  have hDp : 0 < ‖D‖ := by linarith
  change ‖D⁻¹‖ ≤ _ ∧ ‖D⁻¹‖ ≤ _
  rw [norm_inv, inv_eq_one_div]
  constructor
  · apply (div_le_iff₀ hDp).mpr
    nlinarith
  · rw [div_le_div_iff₀ hDp (by positivity), Complex.normSq_eq_norm_sq]
    nlinarith

private theorem collapsed_kernel_bound (x z : ℂ) (hx : ‖x‖ ≤ 1 / 2)
    (hz : ‖z‖ ≤ 1 / 4) :
    (1 - z) ^ 2 + x * z ≠ 0 ∧
      ‖x * (1 + z) / ((1 - z) * ((1 - z) ^ 2 + x * z))‖ ≤ 4 * ‖x‖ := by
  have ha : 3 / 4 ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    norm_num at h
    linarith
  have hb : ‖1 + z‖ ≤ 5 / 4 := by
    exact (norm_add_le _ _).trans (by simpa using (by linarith : 1 + ‖z‖ ≤ 5 / 4))
  have hc : ‖x‖ * ‖z‖ ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 2 : ℝ) * (1 / 4) := mul_le_mul hx hz (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hd : 7 / 16 ≤ ‖(1 - z) ^ 2 + x * z‖ := by
    have h := norm_sub_norm_le ((1 - z) ^ 2) (-(x * z))
    rw [sub_neg_eq_add, norm_neg, norm_pow, norm_mul] at h
    nlinarith [norm_nonneg (1 - z)]
  have hd0 : (1 - z) ^ 2 + x * z ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨hd0, ?_⟩
  have hden : 21 / 64 ≤ ‖1 - z‖ * ‖(1 - z) ^ 2 + x * z‖ := by
    have h := mul_le_mul ha hd (by norm_num : (0 : ℝ) ≤ 7 / 16) (norm_nonneg _)
    norm_num at h
    exact h
  rw [norm_div, norm_mul, norm_mul]
  calc
    _ ≤ (‖x‖ * (5 / 4)) / (‖1 - z‖ * ‖(1 - z) ^ 2 + x * z‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        (by positivity)
    _ ≤ (‖x‖ * (5 / 4)) / (21 / 64) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ 4 * ‖x‖ := by nlinarith [norm_nonneg x]

private theorem kernel_tail_bound (Z : ZeroData) (k : ℕ) (hk : 2 ≤ ‖Z.gamma k‖)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / 4) :
    ‖kernel Z k z‖ ≤ 4 * ((Z.multiplicity k : ℝ) /
      (1 + Complex.normSq (Z.gamma k))) := by
  let x := (Z.zero k * (1 - Z.zero k))⁻¹
  have hx := inverse_product_bound Z k hk
  have hbound := collapsed_kernel_bound x z hx.1 hz
  have hrel := ratio_relations (Z.zero k) (zero_ne Z k).1 (zero_ne Z k).2
  simp only [ratio] at hrel
  have hz0 : 1 - z ≠ 0 := by
    intro he
    have he' : z = 1 := (sub_eq_zero.mp he).symm
    simp [he'] at hz
  rw [kernel, kernel_collapse _ _ x z hrel.1 hrel.2 hz0 hbound.1,
    norm_mul, norm_div, Complex.norm_natCast]
  norm_num only [norm_ofNat]
  calc
    _ ≤ ((Z.multiplicity k : ℝ) / 2) * (4 * ‖x‖) :=
      mul_le_mul_of_nonneg_left hbound.2 (by positivity)
    _ ≤ ((Z.multiplicity k : ℝ) / 2) *
        (4 * (2 / (1 + Complex.normSq (Z.gamma k)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 (by norm_num))
        (by positivity)
    _ = _ := by ring

private theorem pole_factors (Z : ZeroData) (k : ℕ) (z : ℂ) (hz : 1 - z ≠ 0)
    (hs : xiReading ((1 - z)⁻¹) ≠ 0) :
    1 - ratio (Z.zero k) * z ≠ 0 ∧ 1 - ratio (1 - Z.zero k) * z ≠ 0 := by
  have hzero : xiReading (Z.zero k) = 0 :=
    (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
      _).mpr (zeroEquiv Z k).property
  have hp : (1 - z)⁻¹ - Z.zero k ≠ 0 := by
    intro he
    exact hs ((congrArg xiReading (sub_eq_zero.mp he)).trans hzero)
  have hm : (1 - z)⁻¹ - (1 - Z.zero k) ≠ 0 := by
    intro he
    apply hs
    rw [sub_eq_zero.mp he, xi_reading_reflection]
    exact hzero
  have hid (rho : ℂ) (h0 : rho ≠ 0) :
      ((1 - z)⁻¹ - (1 - rho)) * (1 - z) = rho * (1 - ratio rho * z) := by
    dsimp [ratio]
    field_simp [hz, h0]
    ring
  constructor
  · intro he
    exact mul_ne_zero hm hz (by rw [hid _ (zero_ne Z k).1, he, mul_zero])
  · intro he
    have h := hid (1 - Z.zero k) (zero_ne Z k).2
    have heq : 1 - (1 - Z.zero k) = Z.zero k := by ring
    rw [heq, he, mul_zero] at h
    exact mul_ne_zero hp hz h

private theorem kernel_hasSum (Z : ZeroData) (z : ℂ) (hz : 1 - z ≠ 0)
    (hs : xiReading ((1 - z)⁻¹) ≠ 0) :
    HasSum (fun k => kernel Z k z) (liGenerator z) := by
  let s : ℂ := (1 - z)⁻¹
  have hs' : xiReading (1 - s) ≠ 0 := by rw [xi_reading_reflection]; exact hs
  have h := ((xi_reading_normalized_resolvent_hasSum Z s hs).sub
    (xi_reading_normalized_resolvent_hasSum Z (1 - s) hs')).mul_left
      ((1 - z)⁻¹ ^ 2 / 2)
  have hv : (1 - z)⁻¹ ^ 2 / 2 *
      ((logDeriv xiReading s - logDeriv xiReading 0) -
        (logDeriv xiReading (1 - s) - logDeriv xiReading 0)) = liGenerator z := by
    rw [xi_logDeriv_reflection]
    dsimp [liGenerator, s]
    ring
  rw [hv] at h
  apply h.congr_fun
  intro k
  have h0 := (zero_ne Z k).1
  have h1 := (zero_ne Z k).2
  have hq := (pole_factors Z k z hz hs).1
  have hr := (pole_factors Z k z hz hs).2
  have hp : s - Z.zero k ≠ 0 := by
    intro he
    apply hs
    rw [sub_eq_zero.mp he]
    exact (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
      _).mpr (zeroEquiv Z k).property
  have hm : 1 - s - Z.zero k ≠ 0 := by
    intro he
    apply hs'
    rw [sub_eq_zero.mp he]
    exact (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
      _).mpr (zeroEquiv Z k).property
  dsimp [kernel, ratio, s] at *
  field_simp [hz, h0, h1, hq, hr, hp, hm]
  <;> ring

private theorem kernel_differentiable (Z : ZeroData) (k : ℕ) (U : Set ℂ)
    (hz : ∀ z ∈ U, 1 - z ≠ 0)
    (hs : ∀ z ∈ U, xiReading ((1 - z)⁻¹) ≠ 0) :
    DifferentiableOn ℂ (kernel Z k) U := by
  intro z hzu
  have h1 := hz z hzu
  have hq := (pole_factors Z k z h1 (hs z hzu)).1
  have hr := (pole_factors Z k z h1 (hs z hzu)).2
  apply DifferentiableAt.differentiableWithinAt
  dsimp [kernel]
  fun_prop

private theorem geometric_derivative (a : ℂ) (d : ℕ) :
    iteratedDeriv d (fun z : ℂ => a * (1 - a * z)⁻¹) 0 =
      (d.factorial : ℂ) * a ^ (d + 1) := by
  rw [iteratedDeriv_const_mul_field]
  have he : (fun z : ℂ => (1 - a * z)⁻¹) = fun z => (-a * z + 1)⁻¹ := by
    funext z
    congr 1
    ring
  rw [he, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  simp only [mul_zero, zero_add, one_zpow, mul_one]
  rw [neg_pow a d]
  have hh : (-1 : ℂ) ^ d * (-1) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (d.factorial : ℂ) * ((-1 : ℂ) ^ d * (-1) ^ d) * a ^ (d + 1) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [hh]; ring

private theorem kernel_derivative (Z : ZeroData) (k d : ℕ) :
    iteratedDeriv d (kernel Z k) 0 / (d.factorial : ℂ) =
      (Z.multiplicity k : ℂ) / 2 *
        (2 - ratio (Z.zero k) ^ (d + 1) - ratio (1 - Z.zero k) ^ (d + 1)) := by
  have ha (a : ℂ) : AnalyticAt ℂ (fun z : ℂ => a * (1 - a * z)⁻¹) 0 := by
    apply analyticAt_const.mul
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv (by simp)
  have he : kernel Z k = fun z : ℂ => (Z.multiplicity k : ℂ) / 2 *
      (2 * (1 * (1 - 1 * z)⁻¹) - ratio (Z.zero k) * (1 - ratio (Z.zero k) * z)⁻¹ -
        ratio (1 - Z.zero k) * (1 - ratio (1 - Z.zero k) * z)⁻¹) := by
    funext z
    simp [kernel]
  have hf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub (((ha 1).const_mul 2).sub (ha (ratio (Z.zero k)))).contDiffAt
      (ha _).contDiffAt,
    iteratedDeriv_fun_sub ((ha 1).const_mul 2).contDiffAt (ha _).contDiffAt,
    iteratedDeriv_const_mul_field, geometric_derivative, geometric_derivative,
    geometric_derivative]
  simp only [one_pow]
  field_simp [hf]
  <;> ring

private theorem local_domain : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ∀ z ∈ Metric.ball (0 : ℂ) r, xiReading ((1 - z)⁻¹) ≠ 0 := by
  have hc : ContinuousAt (fun z : ℂ => xiReading ((1 - z)⁻¹)) 0 :=
    xi_reading_differentiable.continuous.continuousAt.comp (by fun_prop)
  have hne : xiReading ((1 - (0 : ℂ))⁻¹) ≠ 0 := by
    simpa [xi_reading_endpoint_values.2]
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_ne hne)
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro z hz
  exact he (y := z) ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _))

private theorem coefficient_hasSum (Z : ZeroData) (d : ℕ) :
    HasSum (fun k : ℕ => (Z.multiplicity k : ℂ) / 2 *
      (2 - ratio (Z.zero k) ^ (d + 1) - ratio (1 - Z.zero k) ^ (d + 1)))
      (canonicalLiCoefficient (d + 1) : ℂ) := by
  classical
  obtain ⟨r, hr, hrsmall, hs⟩ := local_domain
  let U := Metric.ball (0 : ℂ) r
  have hU : IsOpen U := Metric.isOpen_ball
  have hzero : (0 : ℂ) ∈ U := Metric.mem_ball_self hr
  have hzsmall (z : ℂ) (hz : z ∈ U) : ‖z‖ ≤ 1 / 4 := by
    exact (by simpa [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < r).le.trans hrsmall
  have hz (z : ℂ) (hzu : z ∈ U) : 1 - z ≠ 0 := by
    intro he
    have he' : z = 1 := (sub_eq_zero.mp he).symm
    have h := hzsmall z hzu
    simp [he'] at h
  have hweight : Summable (fun k : ℕ =>
      (Z.multiplicity k : ℝ) / (1 + Complex.normSq (Z.gamma k))) := by
    have h := (zeroEquiv Z).summable_iff.mpr (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam)
    refine h.congr fun k => ?_
    change (Zeta23.zeroMult (Z.zero k) : ℝ) /
      (1 + Complex.normSq (Zeta23.gammaOf (Z.zero k))) = _
    rw [← multiplicity_eq_zeroMult, gammaOf_eq_spectralParameter]
    rfl
  have hu := tendstoUniformlyOn_tsum_of_cofinite_eventually (hweight.mul_left 4)
    (f := kernel Z) (s := U) (by
      filter_upwards [(Z.symmetricIndices 2).finite_toSet.compl_mem_cofinite] with k hk z hzu
      apply kernel_tail_bound Z k _ z (hzsmall z hzu)
      have hlt : 2 < ‖Z.gamma k‖ := by simpa using hk
      exact hlt.le)
  let P (A : Finset ℕ) : ℂ → ℂ := fun z => ∑ k ∈ A, kernel Z k z
  have hc : TendstoLocallyUniformlyOn P liGenerator atTop U := by
    apply hu.tendstoLocallyUniformlyOn.congr_right
    intro z hzu
    exact (kernel_hasSum Z z (hz z hzu) (hs z hzu)).tsum_eq
  have hphi (k : ℕ) : DifferentiableOn ℂ (kernel Z k) U :=
    kernel_differentiable Z k U hz hs
  have hd (A : Finset ℕ) : DifferentiableOn ℂ (P A) U :=
    DifferentiableOn.fun_sum fun k _ => hphi k
  have hdn : ∀ j A, DifferentiableOn ℂ (iteratedDeriv j (P A)) U := by
    intro j
    induction j with
    | zero => intro A; simpa using hd A
    | succ j ih =>
      intro A
      simpa only [iteratedDeriv_succ] using (ih A).deriv hU
  have hcn : ∀ j, TendstoLocallyUniformlyOn
      (fun A => iteratedDeriv j (P A)) (iteratedDeriv j liGenerator) atTop U := by
    intro j
    induction j with
    | zero => simpa using hc
    | succ j ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Filter.Eventually.of_forall (hdn j)) hU
  have ht := ((hcn d).tendsto_at hzero).div_const (d.factorial : ℂ)
  rw [generator_taylor_coefficient] at ht
  convert ht using 1
  funext A
  rw [show iteratedDeriv d (P A) 0 =
      ∑ k ∈ A, iteratedDeriv d (kernel Z k) 0 by
    apply iteratedDeriv_fun_sum
    intro k _
    exact ((hphi k).analyticAt (hU.mem_nhds hzero)).contDiffAt,
    Finset.sum_div]
  simp_rw [kernel_derivative]

/-- Every canonical Li coefficient is the absolutely convergent real sum over
all actual nontrivial zeros, with their exact analytic multiplicities. -/
theorem canonical_li_eq_zero_real_sum (Z : ZeroData) (n : ℕ) :
    canonicalLiCoefficient n = ∑' k : ℕ,
      (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re) := by
  cases n with
  | zero => simp [canonical_li_zero]
  | succ d =>
    let f : ℕ → ℝ := fun k =>
      (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ (d + 1)).re)
    have hf : Summable f := li_zero_real_summable Z (d + 1)
    have hrefl : HasSum (fun k => f (Z.reflection k)) (∑' k, f k) :=
      (Z.reflection.hasSum_iff).mpr hf.hasSum
    have hav := (hf.hasSum.add hrefl).div_const 2
    have he := Complex.hasSum_re (coefficient_hasSum Z d)
    have he' : HasSum (fun k => (f k + f (Z.reflection k)) / 2)
        (canonicalLiCoefficient (d + 1)) := by
      apply he.congr_fun
      intro k
      simp [ratio, f, Z.multiplicity_reflection, Z.zero_reflection,
        Complex.mul_re, Complex.div_re]
      <;> ring
    have hv := he'.unique hav
    simpa only [add_self_div_two] using hv

#print axioms canonical_li_eq_zero_real_sum

end D5.S3.Weil.ZeroData.CanonicalLiZeroSum
