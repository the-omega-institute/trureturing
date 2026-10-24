/- GID: D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CompleteChebyshevTailIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalize the actual complete Chebyshev tail from absolute integrability. -/

/-
The actual complete Chebyshev tail identity assumes only absolute integrability
of its error kernel and includes every real endpoint t >= 2.

Reuse: Mathlib's SumCoeff owns the L-series/integral interchange; Dirichlet
owns the actual Mangoldt logarithmic derivative; Harmonic.ZetaAsymp owns
the Laurent constant, the entire normalized factor, and its derivative at 1.
In particular this proof does not infer Euler normalization from residue 1.
The finite endpoint calculation is a direct application of Mathlib's Abel
summation theorem. The existing Mertens Gamma owner remains unchanged in
the frozen downstream consumer; its Euler identification is not reproved.

All private helpers are consumed by complete_chebyshev_tail_identity.
The normalization step is normalized_error_integral, with its actual
damped-kernel dominated-convergence proof.
-/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity

open Real Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

private def K (u : ℝ) : ℝ := (Chebyshev.psi u - u) / u ^ 2

private lemma measurable_K : Measurable K := by
  exact (Chebyshev.psi_mono.measurable.sub measurable_id).div
    (measurable_id.pow_const 2)

private lemma damped_norm_le {s u : ℝ} (hs : 1 ≤ s) (hu : 1 < u) :
    ‖K u * u ^ (1 - s)‖ ≤ |K u| := by
  have hu0 : 0 ≤ u := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0 _)]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Real.rpow_le_one_of_one_le_of_nonpos hu.le (by linarith))

private lemma damped_integrable (h : IntegrableOn K (Ioi 1))
    {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn (fun u : ℝ => K u * u ^ (1 - s)) (Ioi 1) := by
  refine h.abs.mono' (measurable_K.mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact damped_norm_le hs hu

private lemma damped_integral_tendsto (h : IntegrableOn K (Ioi 1)) :
    Tendsto (fun s : ℝ => ∫ u in Ioi 1, K u * u ^ (1 - s))
      (𝓝[>] 1) (𝓝 (∫ u in Ioi 1, K u)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u => |K u|)
    (Eventually.of_forall fun s =>
      (measurable_K.mul (by fun_prop)).aestronglyMeasurable) ?_ h.abs ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact damped_norm_le hs.le hu
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hc : ContinuousAt (fun s : ℝ => K u * u ^ (1 - s)) 1 := by
      fun_prop (disch := positivity)
    simpa only [sub_self, Real.rpow_zero, mul_one] using
      hc.tendsto.mono_left nhdsWithin_le_nhds

private lemma mangoldt_prefix_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  have hsum : (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
    change (∑ k ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt k) = _
    simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [hsum, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
    Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

private lemma psi_mellin_point {s u : ℝ} (hu : 1 < u) :
    Chebyshev.psi u * u ^ (-(s + 1)) = K u * u ^ (1 - s) + u ^ (-s) := by
  have hu0 : 0 < u := by linarith
  have hp : u ^ (1 - s) = u ^ (-(s + 1)) * u ^ 2 := by
    rw [show 1 - s = -(s + 1) + 2 by ring, Real.rpow_add hu0, Real.rpow_two]
  have hq : u ^ (-s) = u ^ (-(s + 1)) * u := by
    rw [show -s = -(s + 1) + 1 by ring, Real.rpow_add hu0, Real.rpow_one]
  rw [hp, hq]
  dsimp [K]
  field_simp [hu0.ne']
  <;> ring

/-- Actual Mangoldt Mellin identity, including the main-term contribution s/(s-1). -/
private lemma mellin_identity (h : IntegrableOn K (Ioi 1))
    {s : ℝ} (hs : 1 < s) :
    -(deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re =
      s / (s - 1) + s * ∫ u in Ioi 1, K u * u ^ (1 - s) := by
  have hrep := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (r := (1 : ℝ)) (s := (s : ℂ))
    (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) < (s : ℂ).re by simpa using hs)
    mangoldt_prefix_bigO (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hL : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) =
      -deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) := by
    simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := (s : ℂ))
        (show 1 < (s : ℂ).re by simpa using hs)
  rw [hL] at hrep
  have hpoint (u : ℝ) (hu : u ∈ Ioi (1 : ℝ)) :
      (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) *
          (u : ℂ) ^ (-((s : ℂ) + 1)) =
        ((Chebyshev.psi u * u ^ (-(s + 1)) : ℝ) : ℂ) := by
    have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
    have hpref :
        (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) =
          (Chebyshev.psi u : ℂ) := by
      rw [show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ by
        simpa only [zero_add] using
          (Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) ⌊u⌋₊)]
      simpa only [Chebyshev.psi] using
        (Complex.ofReal_sum (s := Finset.Ioc 0 ⌊u⌋₊)
          (fun k : ℕ => ArithmeticFunction.vonMangoldt k)).symm
    have hpow : (u : ℂ) ^ (-((s : ℂ) + 1)) =
        ((u ^ (-(s + 1)) : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one] using
        (Complex.ofReal_cpow hu0 (-(s + 1))).symm
    rw [hpref, hpow, ← Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_complex_ofReal] at hrep
  have hreal : -(deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re =
      s * ∫ u in Ioi 1, Chebyshev.psi u * u ^ (-(s + 1)) := by
    have hr := congrArg Complex.re hrep
    simpa only [neg_div, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re] using hr
  have hpint : IntegrableOn (fun u : ℝ => u ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpval : (∫ u : ℝ in Ioi 1, u ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos]
    simp only [Real.one_rpow]
    field_simp [show -s + 1 ≠ 0 by linarith,
      show s - 1 ≠ 0 by linarith]
    <;> ring
  have hsplit : (∫ u in Ioi 1, Chebyshev.psi u * u ^ (-(s + 1))) =
      (∫ u in Ioi 1, K u * u ^ (1 - s)) + 1 / (s - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => psi_mellin_point (s := s) hu),
      integral_add (damped_integrable h hs.le) hpint, hpval]
  rw [hsplit, mul_add] at hreal
  simp only [div_eq_mul_inv, one_mul] at hreal ⊢
  linarith only [hreal]

/-- The finite part is the proved Euler constant, using the entire normalized zeta factor. -/
private lemma regular_logderiv_tendsto :
    Tendsto (fun s : ℝ =>
      (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re + 1 / (s - 1))
      (𝓝[>] 1) (𝓝 Real.eulerMascheroniConstant) := by
  have hc : Tendsto
      (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z)
      (𝓝 (1 : ℂ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    convert ((differentiable_riemannZeta₁.deriv.continuous.tendsto (1 : ℂ)).div
      (differentiable_riemannZeta₁.continuous.tendsto (1 : ℂ))
      (by simp : riemannZeta₁ (1 : ℂ) ≠ 0)) using 1 <;> simp
  have heq :
      (fun z : ℂ => deriv riemannZeta z / riemannZeta z + (z - 1)⁻¹) =ᶠ[𝓝[≠] 1]
        (fun z : ℂ => deriv riemannZeta₁ z / riemannZeta₁ z) := by
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with z hz
    rw [hz]
    ring
  have hreg := (hc.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have hofReal : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt hs)
  have hr := (Complex.continuous_re.tendsto
    (Real.eulerMascheroniConstant : ℂ)).comp (hreg.comp hofReal)
  simpa only [Function.comp_def, Complex.add_re, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div] using hr

/-- The actual Chebyshev error has total mass -1-gamma; no normalization premise is added. -/
private lemma normalized_error_integral (h : IntegrableOn K (Ioi 1)) :
    (∫ u in Ioi 1, K u) = -1 - Real.eulerMascheroniConstant := by
  have hsame :
      (fun s : ℝ =>
        -((deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re + 1 / (s - 1)))
        =ᶠ[𝓝[>] 1]
      (fun s : ℝ => 1 + s * ∫ u in Ioi 1, K u * u ^ (1 - s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hm := mellin_identity h hs
    have hs1 : 1 < s := hs
    have ha : s / (s - 1) - 1 / (s - 1) = 1 := by
      field_simp [show s - 1 ≠ 0 by linarith only [hs1]]
      <;> ring
    linarith only [hm, ha]
  have hright : Tendsto
      (fun s : ℝ => 1 + s * ∫ u in Ioi 1, K u * u ^ (1 - s))
      (𝓝[>] 1) (𝓝 (1 + ∫ u in Ioi 1, K u)) := by
    simpa only [one_mul, id_eq] using tendsto_const_nhds.add
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul (damped_integral_tendsto h))
  have he := tendsto_nhds_unique regular_logderiv_tendsto.neg
    (hright.congr' hsame.symm)
  linarith only [he]

private lemma finite_error_integral (h : IntegrableOn K (Ioi 1))
    {t : ℝ} (ht : 1 ≤ t) :
    (∫ u in 1..t, K u) =
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        Chebyshev.psi t / t - Real.log t := by
  have ht0 : 0 < t := by linarith
  have hd (u : ℝ) (hu : u ∈ Icc (1 : ℝ) t) :
      HasDerivAt (fun x : ℝ => x⁻¹) (-(1 / u ^ 2)) u := by
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    simpa only [one_div] using (hasDerivAt_inv hu0)
  have hci : ContinuousOn (fun u : ℝ => -(1 / u ^ 2)) (Icc 1 t) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    fun_prop (disch := positivity)
  have hdi : IntegrableOn (deriv fun x : ℝ => x⁻¹) (Icc 1 t) := by
    refine hci.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro u hu
    exact (hd u hu).deriv.symm
  have hab := sum_mul_eq_sub_integral_mul₀
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) (by simp) t
    (fun u hu => (hd u hu).differentiableAt) hdi
  have hs :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (n : ℝ)⁻¹ * ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊t⌋₊)]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hprod :
      (∫ u in Ioc (1 : ℝ) t,
        deriv (fun x : ℝ => x⁻¹) u *
          ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, ArithmeticFunction.vonMangoldt n) =
        -(∫ u in Ioc (1 : ℝ) t, Chebyshev.psi u / u ^ 2) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    change deriv (fun x : ℝ => x⁻¹) u *
      (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, ArithmeticFunction.vonMangoldt n) =
        -(Chebyshev.psi u / u ^ 2)
    rw [(hd u ⟨hu.1.le, hu.2⟩).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hs, ← Chebyshev.psi_eq_sum_Icc, hprod] at hab
  have hlogin : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 t := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [uIcc_of_le ht] at hu
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    fun_prop (disch := positivity)
  have hlogi : IntegrableOn (fun u : ℝ => 1 / u) (Ioc 1 t) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hlogin
  have hlogv : (∫ u in Ioc (1 : ℝ) t, 1 / u) = Real.log t := by
    rw [← intervalIntegral.integral_of_le ht,
      integral_one_div_of_pos one_pos ht0]
    simp
  have hpi : IntegrableOn (fun u : ℝ => Chebyshev.psi u / u ^ 2) (Ioc 1 t) := by
    refine ((h.mono_set Ioc_subset_Ioi_self).add hlogi).congr_fun ?_ measurableSet_Ioc
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    dsimp [K]
    field_simp [hu0]
    <;> ring
  have hk : (∫ u in Ioc (1 : ℝ) t, K u) =
      (∫ u in Ioc (1 : ℝ) t, Chebyshev.psi u / u ^ 2) - Real.log t := by
    calc
      _ = ∫ u in Ioc (1 : ℝ) t, (Chebyshev.psi u / u ^ 2 - 1 / u) := by
        refine setIntegral_congr_fun measurableSet_Ioc ?_
        intro u hu
        have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
        dsimp [K]
        field_simp [hu0]
        <;> ring
      _ = _ := by rw [integral_sub hpi hlogi, hlogv]
  rw [intervalIntegral.integral_of_le ht, hk]
  simp only [div_eq_mul_inv] at hab ⊢
  linarith only [hab]

/-- Complete actual Chebyshev tail identity for every real endpoint t >= 2.
The premise is absolute Lebesgue integrability of the actual error kernel.
The finite sum is inclusive and retains every prime power. -/
theorem complete_chebyshev_tail_identity
    (h : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Ioi 1))
    {t : ℝ} (ht : 2 ≤ t) :
    (∫ u in Ioi t, (Chebyshev.psi u - u) / u ^ 2) =
      Chebyshev.psi t / t -
        (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
          Real.log t - 1 - Real.eulerMascheroniConstant := by
  change IntegrableOn K (Ioi 1) at h
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htail : IntegrableOn K (Ioi t) := h.mono_set (Ioi_subset_Ioi ht1)
  have hsplit := intervalIntegral.integral_interval_add_Ioi h htail
  change (∫ u in 1..t, K u) + (∫ u in Ioi t, K u) = (∫ u in Ioi 1, K u) at hsplit
  rw [finite_error_integral h ht1, normalized_error_integral h] at hsplit
  change (∫ u in Ioi t, K u) = _
  linarith only [hsplit]

end
end D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
