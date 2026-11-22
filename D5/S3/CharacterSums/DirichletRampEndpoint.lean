/- GID: D5/S3/CharacterSums/DirichletRampEndpoint
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletRampEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character logarithmic derivatives from the finite Mangoldt ramp and Chebyshev tail. -/

import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # Endpoint bounds for character-weighted Mangoldt ramps

The positive part vanishes at an entering prime power. Keeping the subtracted
constant in each active coefficient gives an exact signed Chebyshev tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set MeasureTheory Filter Finset
open scoped Topology
open D5.S3.Weil.Mertens D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.CharacterSums.DirichletRampEndpoint

/-- The finite ramp uses every prime-power coefficient up to the inclusive floor. -/
def characterRamp {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (mangoldtRamp n x : ℂ) * χ (n : ZMod N)

open Classical in
/-- The host readout subtracts the principal main term and adds the native
logarithmic derivative on the nonprincipal branch. -/
def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  if χ = 1 then
    ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x) -
      x * (log x - 1 - eulerMascheroniConstant) : ℝ)
  else characterRamp χ x + (x : ℂ) * (deriv χ.LFunction 1 / χ.LFunction 1)

private theorem normalized_ramp {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    ‖characterRamp χ x‖ / x ≤
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        Chebyshev.psi x / x := by
  have hsum : ‖characterRamp χ x‖ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mangoldtRamp_nonneg n x)]
    exact mul_le_of_le_one_right (mangoldtRamp_nonneg n x) (χ.norm_le_one _)
  have heq : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x) =
      x * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        Chebyshev.psi x := by
    have h := U_eq_complete_ramps hx.le
    have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [U, mangoldtPart_eq_range hx.le (N := ⌊x⌋₊ + 1)
      (by simpa using Nat.lt_floor_add_one x), hrange, Finset.sum_insert (by simp)] at h
    simp [mangoldtRamp] at h ⊢
    linarith only [h]
  rw [heq] at hsum
  apply (div_le_iff₀ hx).mpr
  rw [sub_mul, div_mul_cancel₀ _ hx.ne', mul_comm]
  exact hsum

private theorem endpoint_of_two_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ ‖gChi χ x‖ / x + log x - 1 -
      eulerMascheroniConstant - ∫ u in Set.Ioi x, (Chebyshev.psi u - u) / u ^ 2 := by
  have hx0 : 0 < x := by linarith
  have heq : (x : ℂ) * (deriv χ.LFunction 1 / χ.LFunction 1) =
      gChi χ x - characterRamp χ x := by simp [gChi, hχ]
  have hn := norm_sub_le (gChi χ x) (characterRamp χ x)
  rw [← heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at hn
  have hd : ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤
      ‖gChi χ x‖ / x + ‖characterRamp χ x‖ / x := by
    rw [← add_div, le_div_iff₀ hx0, mul_comm]
    exact hn
  have ht := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  linarith only [hd, normalized_ramp χ hx0, ht]

private theorem kernel_eq_neg_inv {x : ℝ} (hx : 0 < x) :
    (Ioo x 2).EqOn psiErrorKernel (fun u : ℝ => -(u⁻¹)) := by
  intro u hu
  simp only [psiErrorKernel, Chebyshev.psi_eq_zero_of_lt_two hu.2, zero_sub, neg_div]
  field_simp [(hx.trans hu.1).ne']

private theorem kernel_integrable_pos {x : ℝ} (hx : 0 < x) (h2 : x < 2) :
    IntegrableOn psiErrorKernel (Ioi x) := by
  have htail : IntegrableOn psiErrorKernel (Ioi 2) :=
    WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi (by norm_num))
  have hrecip : IntervalIntegrable (fun u : ℝ => -(u⁻¹)) volume x 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h2.le]
    exact (continuousOn_inv₀.mono (fun u hu => ne_of_gt (hx.trans_le hu.1))).neg
  have hinterval : IntervalIntegrable psiErrorKernel volume x 2 := by
    rw [intervalIntegrable_congr_uIoo (show (uIoo x 2).EqOn psiErrorKernel (fun u : ℝ => -(u⁻¹)) by
      simpa only [uIoo_of_le h2.le] using kernel_eq_neg_inv hx)]
    exact hrecip
  rw [← Ioc_union_Ioi_eq_Ioi h2.le]
  exact hinterval.1.union htail

/-- The signed Chebyshev tail gives the exact untwisted envelope at the same real
endpoint, uniformly in every nonprincipal character of positive modulus. -/
theorem logDerivative_le_ramp_tail {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ ‖gChi χ x‖ / x + log x - 1 -
      eulerMascheroniConstant - ∫ u in Set.Ioi x, (Chebyshev.psi u - u) / u ^ 2 := by
  change _ ≤ _ - ∫ u in Ioi x, psiErrorKernel u
  by_cases hx2 : 2 ≤ x
  · exact endpoint_of_two_le χ hχ hx2
  push Not at hx2
  have hg : ‖gChi χ x‖ / x = ‖deriv χ.LFunction 1 / χ.LFunction 1‖ := by
    have hr : characterRamp χ x = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hn
      have hc := (Nat.cast_le.mpr hb).trans (Nat.floor_le hx.le)
      have hd : n < 2 := by exact_mod_cast hc.trans_lt hx2
      have he : n = 1 := by omega
      simp [he, mangoldtRamp]
    simp [gChi, hχ, hr, Real.norm_of_nonneg hx.le, mul_div_cancel_left₀ _ hx.ne']
  have htail : IntegrableOn psiErrorKernel (Ioi 2) :=
    WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi (kernel_integrable_pos hx hx2) htail
  have hpart : (∫ u in x..(2 : ℝ), psiErrorKernel u) = log x - log 2 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hx2.le (kernel_eq_neg_inv hx),
      intervalIntegral.integral_neg, integral_inv_of_pos hx (by norm_num),
      Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
    ring
  have ht := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    WeightedPrimeLimit.chebyshev_error_kernel_integrable (show (2:ℝ) ≤ 2 by rfl)
  have hf : Finset.Ioc 0 (2 : ℕ) = {1,2} := by decide
  simp [Chebyshev.psi, hf] at ht
  change (∫ u in Ioi (2:ℝ), psiErrorKernel u) = _ at ht
  linarith only [hg, hsplit, hpart, ht]

/-- A uniform real threshold yields additive Euler normalization from the same
character's sublinear host readout. -/
theorem uniform_logDerivative_of_ramp {ε η : ℝ} (hε : ε < 1 / 2) (hη : 0 < η) :
    ∃ X ≥ (2 : ℝ), ∀ x ≥ X, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → ‖gChi χ x‖ ≤ x ^ (1 / 2 + ε) →
      ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ log x - 1 - eulerMascheroniConstant + η := by
  have hpow := tendsto_rpow_neg_atTop (sub_pos.mpr hε)
  have htail : Tendsto (fun x : ℝ => ∫ u in Set.Ioi x, (Chebyshev.psi u - u) / u ^ 2)
      atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hp := hpow.eventually_lt_const (show (0 : ℝ) < η / 2 by positivity)
  have ht := htail.eventually_const_lt (show -(η / 2) < (0 : ℝ) by linarith)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hp.and ht)
  refine ⟨max 2 A, le_max_left _ _, ?_⟩
  intro x hx N _ χ hχ hg
  have hx2 := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hpp, htt⟩ := hA x ((le_max_right _ _).trans hx)
  have heq : x ^ ((1 : ℝ) / 2 + ε) / x = x ^ (-(1 / 2 - ε)) := by
    rw [show -(1 / 2 - ε) = (1 / 2 + ε) - 1 by ring, Real.rpow_sub hx0, Real.rpow_one]
  have hnorm := div_le_div_of_nonneg_right hg hx0.le
  rw [heq] at hnorm
  have hfinite := logDerivative_le_ramp_tail χ hχ hx0
  change x ^ (-(1 / 2 - ε)) < η / 2 at hpp
  change -(η / 2) < ∫ u in Set.Ioi x, (Chebyshev.psi u - u) / u ^ 2 at htt
  linarith only [hnorm, hfinite, hpp, htt]

end D5.S3.CharacterSums.DirichletRampEndpoint
