/- GID: D5/S3/Observer/Linear/ExactTaylorObservationRemainder
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/ExactTaylorObservationRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.Exponential, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: Exact factorial Taylor remainder bounds for bounded continuous-time observations on arbitrary Banach state spaces. -/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.ExactTaylorObservationRemainder

open MeasureTheory Finset
open scoped BigOperators

theorem exp_tail_le {𝕜 A : Type*} [RCLike 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] [NormOneClass A] (z : A) (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖NormedSpace.exp z - ∑ k ∈ range n, ((k.factorial : 𝕜)⁻¹) • z ^ k‖ ≤
      r ^ n / (n.factorial : ℝ) * Real.exp r := by
  let f : ℕ → A := fun k => ((k.factorial : 𝕜)⁻¹) • z ^ k
  have hs : HasSum f (NormedSpace.exp z) := NormedSpace.exp_series_hasSum_exp' z
  have ht : HasSum (fun k => f (k + n))
      (NormedSpace.exp z - ∑ k ∈ range n, f k) := by
    apply (hasSum_nat_add_iff n).2
    simpa only [sub_add_cancel] using hs
  have he : HasSum (fun k : ℕ => r ^ n / (n.factorial : ℝ) *
      (r ^ k / (k.factorial : ℝ))) (r ^ n / (n.factorial : ℝ) * Real.exp r) := by
    simpa only [Real.exp_eq_exp_ℝ, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (NormedSpace.expSeries_div_hasSum_exp r).mul_left (r ^ n / (n.factorial : ℝ))
  apply ht.norm_le_of_bounded he
  intro k
  have hfac : (n.factorial : ℝ) * (k.factorial : ℝ) ≤ ((k + n).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (k + n))
      (by simpa only [Nat.add_comm] using Nat.factorial_mul_factorial_dvd_factorial_add n k)
  calc
    ‖f (k + n)‖ = ‖z ^ (k + n)‖ / ((k + n).factorial : ℝ) := by
      simp [f, norm_smul, div_eq_mul_inv, mul_comm]
    _ ≤ r ^ (k + n) / ((k + n).factorial : ℝ) := by
      gcongr
      exact (norm_pow_le z _).trans (pow_le_pow_left₀ (norm_nonneg _) hz _)
    _ ≤ r ^ (k + n) / ((n.factorial : ℝ) * (k.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (pow_nonneg hr _) (by positivity) hfac
    _ = r ^ n / (n.factorial : ℝ) * (r ^ k / (k.factorial : ℝ)) := by
      rw [pow_add]
      ring

/-- The actual Taylor observation polynomial, including the zeroth derivative. -/
def observationTaylor {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (t : ℝ) (x : V) : W :=
  ∑ k ∈ range (N + 1), ((t ^ k / (k.factorial : ℝ) : ℝ) : 𝕜) • C ((B ^ k) x)

/-- An exact factorial bound for the observed exponential tail. The state and
output may be infinite dimensional, over either the real or complex field. -/
theorem norm_observation_taylor_remainder {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : V) :
    ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ≤
      ‖C‖ * Real.exp (max 1 ‖B‖ * t) * (max 1 ‖B‖ * t) ^ (N + 1) /
        ((N + 1).factorial : ℝ) * ‖x‖ := by
  let b : ℝ := max 1 ‖B‖
  have hb : 0 ≤ b := le_trans (by norm_num) (le_max_left _ _)
  have he := exp_tail_le (𝕜 := 𝕜) ((t : 𝕜) • B) (b * t) (N + 1) (mul_nonneg hb ht) (by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) ht).trans_eq (mul_comm _ _))
  have hpoly : C ((∑ k ∈ range (N + 1),
      ((k.factorial : 𝕜)⁻¹) • ( (t : 𝕜) • B) ^ k) x) = observationTaylor B C N t x := by
    simp only [observationTaylor, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_pow, smul_smul, map_sum, map_smul,
      RCLike.ofReal_div, RCLike.ofReal_pow, RCLike.ofReal_natCast]
    apply sum_congr rfl
    intro k _
    congr 1
    ring
  rw [← hpoly, ← map_sub, ← ContinuousLinearMap.sub_apply]
  calc
    _ ≤ ‖C‖ * ‖(NormedSpace.exp ((t : 𝕜) • B) -
        ∑ k ∈ range (N + 1), ((k.factorial : 𝕜)⁻¹) • ( (t : 𝕜) • B) ^ k) x‖ := C.le_opNorm _
    _ ≤ ‖C‖ * (‖NormedSpace.exp ((t : 𝕜) • B) -
        ∑ k ∈ range (N + 1), ((k.factorial : 𝕜)⁻¹) • ( (t : 𝕜) • B) ^ k‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ x) (norm_nonneg _)
    _ ≤ ‖C‖ * ((b * t) ^ (N + 1) / ((N + 1).factorial : ℝ) * Real.exp (b * t) * ‖x‖) := by
      gcongr
    _ = _ := by dsimp [b]; ring

/-- Squared trajectory-error energy on every nonnegative window, with the
factorial and integration constants retained exactly. -/
theorem observation_taylor_energy_remainder {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : V) :
    (∫ t in (0 : ℝ)..T,
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2) ≤
      (‖C‖ * Real.exp (max 1 ‖B‖ * T) * max 1 ‖B‖ ^ (N + 1) /
        ((N + 1).factorial : ℝ)) ^ 2 *
        (T ^ (2 * N + 3) / (2 * N + 3 : ℕ)) * ‖x‖ ^ 2 := by
  let b : ℝ := max 1 ‖B‖
  let K : ℝ := ‖C‖ * Real.exp (b * T) * b ^ (N + 1) /
    ((N + 1).factorial : ℝ) * ‖x‖
  have hb : 0 ≤ b := le_trans (by norm_num) (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly : Continuous (fun t : ℝ => observationTaylor B C N t x) := by
    unfold observationTaylor
    fun_prop
  have hexp : Continuous (fun t : ℝ =>
      C ((NormedSpace.exp ((t : 𝕜) • B)) x)) := by
    exact C.continuous.comp
      ((ContinuousLinearMap.apply 𝕜 V x).continuous.comp
        ((continuous_iff_continuousAt.mpr (fun z =>
          (NormedSpace.exp_analytic (𝕂 := 𝕜) z).continuousAt)).comp
          ((RCLike.continuous_ofReal : Continuous (fun t : ℝ => (t : 𝕜))).smul
            continuous_const)))
  have herror : Continuous (fun t : ℝ =>
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2) :=
    (hexp.sub hpoly).norm.pow 2
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ^ 2 ≤
        K ^ 2 * t ^ (2 * N + 2) := by
    have ht0 : 0 ≤ t := ht.1
    have hh := norm_observation_taylor_remainder B C N t ht.1 x
    have hn : ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) -
        observationTaylor B C N t x‖ ≤ K * t ^ (N + 1) := by
      calc
        _ ≤ ‖C‖ * Real.exp (b * t) * (b * t) ^ (N + 1) /
            ((N + 1).factorial : ℝ) * ‖x‖ := hh
        _ ≤ ‖C‖ * Real.exp (b * T) * (b * t) ^ (N + 1) /
            ((N + 1).factorial : ℝ) * ‖x‖ := by
          gcongr <;> first | positivity | exact hb | exact ht.1 | exact ht.2
        _ = K * t ^ (N + 1) := by dsimp [K]; rw [mul_pow]; ring
    have hh2 := mul_self_le_mul_self (norm_nonneg _) hn
    simpa only [← pow_two, mul_pow, ← pow_mul, show (N + 1) * 2 = 2 * N + 2 by omega]
      using hh2
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, K ^ 2 * t ^ (2 * N + 2) :=
      intervalIntegral.integral_mono_on hT (herror.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => K ^ 2 * t ^ (2 * N + 2))).intervalIntegrable _ _)
          hpoint
    _ = K ^ 2 * (T ^ (2 * N + 3) / (2 * N + 3 : ℕ)) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      have hdegree : 2 * N + 2 + 1 = 2 * N + 3 := by omega
      have hden : (↑(2 * N + 2) : ℝ) + 1 = ↑(2 * N + 3) := by push_cast; ring
      rw [hdegree, hden, zero_pow (by omega : 2 * N + 3 ≠ 0), sub_zero]
    _ = _ := by dsimp [K, b]; ring

end D5.S3.Observer.Linear.ExactTaylorObservationRemainder
