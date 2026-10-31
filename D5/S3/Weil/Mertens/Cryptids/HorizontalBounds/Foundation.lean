/- GID: D5/S3/Weil/Mertens/Cryptids/HorizontalBounds/Foundation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/HorizontalBounds/Foundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids HorizontalBounds analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/HorizontalBounds.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.DigammaBinet
import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! Original HorizontalBounds analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.HorizontalBounds

export ConjectureMachines.Semantics.Riemann.DigammaBinet
  (ofReal_ne_neg_natCast_of_pos ne_neg_natCast_of_re_pos deriv_Gamma_ofReal_eq digamma_ofReal_eq_deriv_log_Gamma digamma_ofReal_re
   digamma_add_one_re_sandwich digamma_ofReal_re_sandwich norm_digamma_ofReal_sub_log_le tendsto_digamma_add_nat_sub_log sawtoothB1
   abs_sawtoothB1_le_half measurable_sawtoothB1 binetIntegrand binetIntegrand_eq_sawtoothB1 add_ofReal_mem_slitPlane
   re_add_le_norm_add_ofReal add_ofReal_ne_zero norm_binetIntegrand_le integral_Ioi_one_div_add_sq integrableOn_Ioi_one_div_add_sq
   measurable_binetIntegrand integrableOn_Ioi_binetIntegrand intervalIntegrable_binetIntegrand eulerMaclaurinAntideriv hasDerivAt_eulerMaclaurinAntideriv
   intervalIntegral_eulerMaclaurin_unit intervalIntegral_binetIntegrand_unit intervalIntegral_binetIntegrand_range digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem digamma_ofReal_eq_eulerMaclaurin
   differentiableOn_integral_binetIntegrand differentiableOn_digamma_rightHalfPlane digamma_eq_log_sub_half_inv_sub_integral norm_digamma_sub_log_add_half_inv_le_re norm_digamma_sub_log_le_norm_add_re)

export RiemannSchmidt
  (fractKernel sub_floor_bounds norm_fractKernel_le_one measurable_fractKernel locallyIntegrableOn_fractKernel
   isBigO_fractKernel_atTop isBigO_fractKernel_nhdsGT_zero mellinConvergent_fractKernel differentiableAt_mellin_fractKernel differentiableAt_mul_mellin_fractKernel_neg
   mellin_fractKernel_neg_eq riemannZeta_eq_mul_integral_floor integral_Ioi_one_mul_cpow_neg_add_one one_sub_riemannZeta₀_eq_of_one_lt_re one_sub_riemannZeta₀_eq_of_re_pos)

export ConjectureMachines.Semantics.Riemann.VonMangoldtCount
  (isPreconnected_re_pos analyticOnNhd_riemannZeta₁ analyticOrderAt_riemannZeta₁_ne_top IsNontrivialZetaZero isNontrivialZetaZero_ne_zero
   re_lt_one_of_isNontrivialZetaZero zero_lt_re_of_isNontrivialZetaZero mem_criticalStrip_of_isNontrivialZetaZero finite_nontrivialZetaZeros_le nontrivialZetaZerosUpTo
   mem_nontrivialZetaZerosUpTo)

open Complex Filter MeasureTheory Set Asymptotics Metric MeromorphicOn ComplexConjugate
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- For `0 < a`, `∫ t in Ioi 1, t ^ (-(a + 1)) = 1 / a`. -/
theorem integral_Ioi_one_rpow_neg_add_one {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (1 : ℝ), t ^ (-(a + 1)) = 1 / a := by
  have hlt : -(a + 1) < -1 := by linarith
  rw [integral_Ioi_rpow_of_lt hlt zero_lt_one]
  have h1 : -(a + 1) + 1 = -a := by ring
  rw [Real.one_rpow, h1, div_neg, neg_div, neg_neg, one_div]

/-- For every `s : ℂ` with `0 < s.re`, `‖mellin fractKernel (-s)‖ ≤ 1 / s.re`. -/
theorem norm_mellin_fractKernel_neg_le {s : ℂ} (hs : 0 < s.re) :
    ‖mellin fractKernel (-s)‖ ≤ 1 / s.re := by
  rw [mellin_fractKernel_neg_eq, ← integral_Ioi_one_rpow_neg_add_one hs]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine norm_integral_le_of_norm_le
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos ht_pos]
  obtain ⟨h0, h1⟩ := sub_floor_bounds ht_pos.le
  rw [abs_of_nonneg h0, show (-(s + 1)).re = -(s.re + 1) by simp]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht_pos.le _) h1

/-- For every `s : ℂ` with `0 < s.re`, `‖1 - riemannZeta₀ s‖ ≤ ‖s‖ / s.re`. -/
theorem norm_one_sub_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖1 - riemannZeta₀ s‖ ≤ ‖s‖ / s.re := by
  rw [one_sub_riemannZeta₀_eq_of_re_pos hs, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_mellin_fractKernel_neg_le hs) (norm_nonneg s)

/-- For every `s : ℂ` with `0 < s.re`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re`. -/
theorem norm_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  have h1 : ‖riemannZeta₀ s‖ ≤ 1 + ‖1 - riemannZeta₀ s‖ := by
    calc
      ‖riemannZeta₀ s‖ = ‖1 - (1 - riemannZeta₀ s)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖1 - riemannZeta₀ s‖ := norm_sub_le 1 (1 - riemannZeta₀ s)
      _ = 1 + ‖1 - riemannZeta₀ s‖ := by rw [norm_one]
  linarith [norm_one_sub_riemannZeta₀_le hs]

/-- **Explicit Upper Bound on `riemannZeta₁ s`**:
For every `s : ℂ` with `0 < s.re`, `‖riemannZeta₁ s‖ ≤ 1 + ‖s - 1‖ * (1 + ‖s‖ / s.re)`. -/
theorem norm_riemannZeta₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ 1 + ‖s - 1‖ * (1 + ‖s‖ / s.re) := by
  unfold riemannZeta₁
  have h1 : ‖1 + (s - 1) * riemannZeta₀ s‖ ≤ 1 + ‖s - 1‖ * ‖riemannZeta₀ s‖ := by
    calc
      ‖1 + (s - 1) * riemannZeta₀ s‖
        ≤ ‖(1 : ℂ)‖ + ‖(s - 1) * riemannZeta₀ s‖ := norm_add_le _ _
      _ = 1 + ‖s - 1‖ * ‖riemannZeta₀ s‖ := by rw [norm_one, norm_mul]
  have h2 : ‖s - 1‖ * ‖riemannZeta₀ s‖ ≤ ‖s - 1‖ * (1 + ‖s‖ / s.re) :=
    mul_le_mul_of_nonneg_left (norm_riemannZeta₀_le hs) (norm_nonneg _)
  linarith

/-- For every `s : ℂ` with `0 < s.re` and `s ≠ 1`,
`‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by
  rw [riemannZeta_eq_inv_sub_add hs1]
  have h1 : ‖(s - 1)⁻¹ + riemannZeta₀ s‖ ≤ 1 / ‖s - 1‖ + ‖riemannZeta₀ s‖ := by
    calc
      ‖(s - 1)⁻¹ + riemannZeta₀ s‖
        ≤ ‖(s - 1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ = 1 / ‖s - 1‖ + ‖riemannZeta₀ s‖ := by rw [norm_inv, one_div]
  linarith [norm_riemannZeta₀_le hs]

/-- For `1 < s.re`, the Möbius L-series satisfies
`‖L ↗ArithmeticFunction.moebius s‖ ≤ 1 / (s.re - 1) + 2`. -/
theorem norm_LSeries_moebius_le {s : ℂ} (hs : 1 < s.re) :
    ‖L ↗ArithmeticFunction.moebius s‖ ≤ 1 / (s.re - 1) + 2 := by
  have h_sum_one : LSeriesSummable 1 (s.re : ℂ) :=
    LSeriesSummable_one_iff.mpr (by simpa using hs)
  have h_term_le : ∀ n : ℕ,
      ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ ≤ (LSeries.term 1 (s.re : ℂ) n).re := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [hn, ↓reduceIte, LSeries.term_of_ne_zero hn, Pi.one_apply,
         ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg n), ← ofReal_one, ← ofReal_div, ofReal_re]
      gcongr
      have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      simpa [Complex.norm_intCast] using hμ
  have h_re_sum : Summable (fun n : ℕ ↦ (LSeries.term 1 (s.re : ℂ) n).re) :=
    (Complex.hasSum_re h_sum_one.hasSum).summable
  have h1 : ‖L ↗ArithmeticFunction.moebius s‖ ≤ ∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re := by
    calc
      ‖L ↗ArithmeticFunction.moebius s‖ ≤
        ∑' n : ℕ, ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ :=
        norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm
      _ ≤ ∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re :=
        Summable.tsum_le_tsum h_term_le
          (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm h_re_sum
  have h2 : (∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re) = (riemannZeta (s.re : ℂ)).re := by
    rw [(Complex.hasSum_re h_sum_one.hasSum).tsum_eq]
    change (L 1 (s.re : ℂ)).re = _
    rw [LSeries_one_eq_riemannZeta (by simpa using hs)]
  have h3 : (riemannZeta (s.re : ℂ)).re ≤ ‖riemannZeta (s.re : ℂ)‖ := re_le_norm _
  have h4 : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 / (s.re - 1) + 2 := by
    have h_pos : 0 < (s.re : ℂ).re := by simp; linarith
    have h_ne1 : (s.re : ℂ) ≠ 1 := by exact_mod_cast hs.ne'
    have h_b := norm_riemannZeta_le h_pos h_ne1
    have h_sub : ‖(s.re : ℂ) - 1‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
    have h_norm : ‖(s.re : ℂ)‖ = s.re := by
      rw [norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h_sub, h_norm, ofReal_re, div_self (by linarith)] at h_b
    linarith
  linarith

/-- For every `s : ℂ` with `1 < s.re`, `(s.re - 1) / (2 * s.re - 1) ≤ ‖riemannZeta s‖`. -/
theorem le_norm_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / (2 * s.re - 1) ≤ ‖riemannZeta s‖ := by
  have h_inv : riemannZeta s * L ↗ArithmeticFunction.moebius s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have h_norm_mul : ‖riemannZeta s‖ * ‖L ↗ArithmeticFunction.moebius s‖ = 1 := by
    simpa [norm_mul] using congrArg norm h_inv
  have h_mu := norm_LSeries_moebius_le hs
  have h_rhs : 1 / (s.re - 1) + 2 = (2 * s.re - 1) / (s.re - 1) := by
    have : s.re - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h_rhs] at h_mu
  have h_zeta_pos : 0 < ‖riemannZeta s‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have h_denom_pos : 0 < 2 * s.re - 1 := by linarith
  have h_sub_pos : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ h_denom_pos]
  have h_le : 1 ≤ ‖riemannZeta s‖ * ((2 * s.re - 1) / (s.re - 1)) := by
    calc
      1 = ‖riemannZeta s‖ * ‖L ↗ArithmeticFunction.moebius s‖ := h_norm_mul.symm
      _ ≤ ‖riemannZeta s‖ * ((2 * s.re - 1) / (s.re - 1)) :=
        mul_le_mul_of_nonneg_left h_mu h_zeta_pos.le
  rw [mul_div_assoc', le_div_iff₀ h_sub_pos, one_mul] at h_le
  exact h_le

/-- On the vertical line `s.re = 2`, `1 / 3 ≤ ‖riemannZeta s‖`. -/
theorem one_third_le_norm_riemannZeta_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  have h := le_norm_riemannZeta_of_one_lt_re (s := s) (by linarith)
  rw [hs] at h
  norm_num at h
  exact h

/-- On the vertical line `s.re = 2`, `1 / 3 ≤ ‖riemannZeta₁ s‖`. -/
theorem one_third_le_norm_riemannZeta₁_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta₁ s‖ := by
  have hs1 : s ≠ 1 := by intro h; subst h; simp at hs
  have h_eq : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  have h_sub : 1 ≤ ‖s - 1‖ := by
    calc
      (1 : ℝ) = (s - 1).re := by simp [hs]; ring
      _ ≤ ‖s - 1‖ := re_le_norm (s - 1)
  rw [h_eq, norm_mul]
  calc
    (1 / 3 : ℝ) = 1 * (1 / 3) := by ring
    _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
      mul_le_mul h_sub (one_third_le_norm_riemannZeta_of_re_eq_two hs) (by positivity)
        (norm_nonneg _)

/-!
## Section 1: Nonvanishing of `riemannZeta` and `riemannZeta₁` on `{s : ℂ | 1 / 2 < s.re}` under RH
-/

/-- The holomorphic branch of `log (riemannZeta₁ w / riemannZeta₁ (2 + t * I))` on
`Metric.ball (2 + t * I) (3 / 2)`, constructed via `Complex.wedgeIntegral` of
`deriv riemannZeta₁ / riemannZeta₁` from the basepoint `2 + t * I`. -/
noncomputable def logRiemannZeta₁Branch (t : ℝ) (w : ℂ) : ℂ :=
  Complex.wedgeIntegral (2 + (t : ℂ) * I) w (fun z ↦ deriv riemannZeta₁ z / riemannZeta₁ z)

/-- At the center `2 + t * I`, `logRiemannZeta₁Branch t (2 + t * I) = 0`. -/
@[simp]
theorem logRiemannZeta₁Branch_self (t : ℝ) :
    logRiemannZeta₁Branch t (2 + (t : ℂ) * I) = 0 := by
  simp [logRiemannZeta₁Branch, Complex.wedgeIntegral]

/-- **Centered Borel–Carathéodory Theorem on `Metric.ball c R`**:
If `f` is complex-differentiable on `Metric.ball c R` (`0 < R`), `f c = 0`, and `(f w).re ≤ M`
(`0 < M`) for all `w ∈ Metric.ball c R`, then for every `z ∈ Metric.ball c R`,
`‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖)`. -/
theorem borelCaratheodory_ball {c z : ℂ} {R M : ℝ} {f : ℂ → ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : ∀ w ∈ Metric.ball c R, (f w).re ≤ M) (hR : 0 < R)
    (hz : z ∈ Metric.ball c R) (hf₂ : f c = 0) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  let g : ℂ → ℂ := fun u ↦ f (c + u)
  have h_maps_ball : MapsTo (fun u : ℂ ↦ c + u) (Metric.ball 0 R) (Metric.ball c R) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    rw [mem_ball_iff_norm, add_sub_cancel_left]
    exact hu
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 R) :=
    hf.comp (differentiable_id.const_add c).differentiableOn h_maps_ball
  have hg_re : MapsTo g (Metric.ball 0 R) {w : ℂ | w.re ≤ M} :=
    fun u hu ↦ hf₁ (c + u) (h_maps_ball hu)
  have hz0 : z - c ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    exact mem_ball_iff_norm.mp hz
  have hg0 : g 0 = 0 := by simp [g, hf₂]
  have h_bc := Complex.borelCaratheodory_zero hM hg_diff hg_re hR hz0 hg0
  simpa [g] using h_bc

/-- Explicit growth bound for `‖riemannZeta₁ w‖` on `Metric.closedBall (2 + t * I) R`
for `0 ≤ R < 2`. -/
noncomputable def zeta₁BallBound (t R : ℝ) : ℝ :=
  1 + (‖(1 : ℂ) + (t : ℂ) * I‖ + R) * (1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R))

/-- For `0 ≤ R < 2`, `1 ≤ zeta₁BallBound t R`. -/
theorem one_le_zeta₁BallBound (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR2 : R < 2) :
    1 ≤ zeta₁BallBound t R := by
  unfold zeta₁BallBound
  have h1 : 0 ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by positivity
  have h2 : 0 ≤ 1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R) :=
    add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith))
  linarith [mul_nonneg h1 h2]

/-- For `0 ≤ R < 2`, `0 < Real.log (3 * zeta₁BallBound t R)`. -/
theorem log_three_mul_zeta₁BallBound_pos (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR2 : R < 2) :
    0 < Real.log (3 * zeta₁BallBound t R) := by
  refine Real.log_pos ?_
  linarith [one_le_zeta₁BallBound t hR hR2]

/-- For `0 ≤ R < 2` and `w ∈ Metric.closedBall (2 + t * I) R`,
`‖riemannZeta₁ w‖ ≤ zeta₁BallBound t R`. -/
theorem norm_riemannZeta₁_le_zeta₁BallBound {t R : ℝ} {w : ℂ}
    (hR : 0 ≤ R) (hR2 : R < 2) (hw : w ∈ Metric.closedBall (2 + (t : ℂ) * I) R) :
    ‖riemannZeta₁ w‖ ≤ zeta₁BallBound t R := by
  let c : ℂ := 2 + (t : ℂ) * I
  rw [mem_closedBall_iff_norm] at hw
  have hw_re : 2 - R ≤ w.re := by
    have h1 : (c - w).re ≤ ‖c - w‖ := re_le_norm (c - w)
    rw [norm_sub_rev] at h1
    have h2 : (c - w).re = 2 - w.re := by simp [c]
    linarith
  have hw_re_pos : 0 < w.re := by linarith
  have hw_norm : ‖w‖ ≤ ‖c‖ + R := by
    calc
      ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + R := by linarith
  have hw_sub_one : ‖w - 1‖ ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by
    have hc1 : c - 1 = (1 : ℂ) + (t : ℂ) * I := by simp [c]; ring
    calc
      ‖w - 1‖ = ‖(c - 1) + (w - c)‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by rw [hc1]; linarith
  have h_div : ‖w‖ / w.re ≤ (‖c‖ + R) / (2 - R) :=
    div_le_div₀ (by positivity) hw_norm (by linarith) hw_re
  refine (norm_riemannZeta₁_le hw_re_pos).trans ?_
  unfold zeta₁BallBound
  gcongr

/-- For every `w : ℂ` with `w ≠ 1` and `riemannZeta₁ w ≠ 0`,
`deriv riemannZeta w / riemannZeta w = deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)`. -/
theorem logDeriv_riemannZeta_eq_sub {w : ℂ} (hw1 : w ≠ 1) (hz1 : riemannZeta₁ w ≠ 0) :
    deriv riemannZeta w / riemannZeta w =
      deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1) := by
  have hw_sub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have h_ev : riemannZeta =ᶠ[𝓝 w] (fun z ↦ (z - 1)⁻¹ * riemannZeta₁ z) := by
    filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
    exact riemannZeta_eq_inv_sub_mul hz
  have h_deriv_inv : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹) (-1 / (w - 1) ^ 2) w :=
    ((hasDerivAt_id w).sub_const (1 : ℂ)).inv hw_sub
  have h_deriv_prod : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹ * riemannZeta₁ z)
      (-1 / (w - 1) ^ 2 * riemannZeta₁ w + (w - 1)⁻¹ * deriv riemannZeta₁ w) w :=
    h_deriv_inv.mul (differentiable_riemannZeta₁ w).hasDerivAt
  have h_deriv_zeta : deriv riemannZeta w =
      -1 / (w - 1) ^ 2 * riemannZeta₁ w + (w - 1)⁻¹ * deriv riemannZeta₁ w :=
    (h_ev.hasDerivAt_iff.mpr h_deriv_prod).deriv
  rw [h_deriv_zeta, riemannZeta_eq_inv_sub_mul hw1]
  field_simp [hw_sub, hz1]
  ring

/-- Every `w ∈ Metric.ball (2 + U * I) R` with `R < 2` satisfies `0 < w.re`. -/
theorem re_pos_of_mem_ball_two_add_mul_I_of_lt_two {U R : ℝ} {w : ℂ}
    (hR2 : R < 2) (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R) :
    0 < w.re := by
  rw [mem_ball_iff_norm] at hw
  have h1 : (2 + (U : ℂ) * I - w).re ≤ ‖2 + (U : ℂ) * I - w‖ := re_le_norm _
  rw [norm_sub_rev] at h1
  have h2 : (2 + (U : ℂ) * I - w).re = 2 - w.re := by simp
  linarith

/-- **Nonvanishing of `riemannZeta₁` on `Metric.ball (2 + U * I) (3 / 2 + Δ ^ 2 / 4)`
at Zero-Free Height `U`**:
Under `RiemannHypothesis`, if `0 < Δ ≤ 1 / 2` and every critical-line zero `ρ` of `riemannZeta`
satisfies `Δ ≤ |ρ.im - U|`, then `riemannZeta₁ w ≠ 0` for all
`w ∈ Metric.ball (2 + U * I) (3 / 2 + Δ ^ 2 / 4)`. -/
theorem riemannZeta₁_ne_zero_of_mem_ball_of_gap (hRH : RiemannHypothesis) {U Δ : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) (3 / 2 + Δ ^ 2 / 4)) :
    riemannZeta₁ w ≠ 0 := by
  have hR_lt_two : 3 / 2 + Δ ^ 2 / 4 < 2 := by nlinarith
  have hw_re_pos : 0 < w.re := re_pos_of_mem_ball_two_add_mul_I_of_lt_two hR_lt_two hw
  rcases eq_or_ne w 1 with rfl | hw1
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  · intro hz1
    have hz : riemannZeta w = 0 := by
      have h_eq := riemannZeta_eq_inv_sub_mul hw1
      rw [hz1, mul_zero] at h_eq
      exact h_eq
    have htriv : ¬∃ n : ℕ, w = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hre : w.re = 1 / 2 := hRH w hz htriv hw1
    have h_im : Δ ≤ |w.im - U| := hgap w hz hre
    have h_im_sq : Δ ^ 2 ≤ (w.im - U) ^ 2 := by
      have h_abs_sq : Δ ^ 2 ≤ |w.im - U| ^ 2 :=
         pow_le_pow_left₀ hΔ_pos.le h_im 2
      rwa [sq_abs] at h_abs_sq
    rw [mem_ball_iff_norm] at hw
    have hw_sq : ‖w - (2 + (U : ℂ) * I)‖ ^ 2 < (3 / 2 + Δ ^ 2 / 4) ^ 2 :=
      pow_lt_pow_left₀ hw (norm_nonneg _) (by norm_num)
    have h_norm_sq : ‖w - (2 + (U : ℂ) * I)‖ ^ 2 = 9 / 4 + (w.im - U) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h_sub_re : (w - (2 + (U : ℂ) * I)).re = -3 / 2 := by simp [hre]; ring
      have h_sub_im : (w - (2 + (U : ℂ) * I)).im = w.im - U := by simp
      rw [h_sub_re, h_sub_im]
      ring
    rw [h_norm_sq] at hw_sq
    have hΔ4 : Δ ^ 4 ≤ (1 / 4) * Δ ^ 2 := by
      have hΔ2_le : Δ ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [sq_nonneg Δ]
    nlinarith

/-- General holomorphicity of `logRiemannZeta₁Branch U` on any ball `Metric.ball (2 + U * I) R₀`
on which `riemannZeta₁` is nonvanishing. -/
theorem hasDerivAt_logRiemannZeta₁Branch_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    HasDerivAt (logRiemannZeta₁Branch U) (deriv riemannZeta₁ w / riemannZeta₁ w) w := by
  have hd : DifferentiableOn ℂ (fun z ↦ deriv riemannZeta₁ z / riemannZeta₁ z)
      (Metric.ball (2 + (U : ℂ) * I) R₀) := by
    intro z hz
    exact ((differentiable_riemannZeta₁.deriv z).div (differentiable_riemannZeta₁ z)
      (h_ne z hz)).differentiableWithinAt
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hw

/-- General exponential identity for `logRiemannZeta₁Branch U` on `Metric.ball (2 + U * I) R₀`. -/
theorem exp_logRiemannZeta₁Branch_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (hR₀ : 0 < R₀) (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    Complex.exp (logRiemannZeta₁Branch U w) =
      riemannZeta₁ w / riemannZeta₁ (2 + (U : ℂ) * I) := by
  let c : ℂ := 2 + (U : ℂ) * I
  let g : ℂ → ℂ := fun z ↦ riemannZeta₁ z * Complex.exp (-logRiemannZeta₁Branch U z)
  have hg_hasDeriv : ∀ z ∈ Metric.ball c R₀, HasDerivAt g 0 z := by
    intro z hz
    have hz_ne : riemannZeta₁ z ≠ 0 := h_ne z hz
    have h1 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ z) z :=
      (differentiable_riemannZeta₁ z).hasDerivAt
    have h2 : HasDerivAt (fun u ↦ Complex.exp (-logRiemannZeta₁Branch U u))
        (Complex.exp (-logRiemannZeta₁Branch U z) * -(deriv riemannZeta₁ z / riemannZeta₁ z)) z :=
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).neg.cexp
    convert h1.mul h2 using 1
    field_simp [hz_ne]
    ring
  have hg_diff : DifferentiableOn ℂ g (Metric.ball c R₀) :=
    fun z hz ↦ (hg_hasDeriv z hz).differentiableAt.differentiableWithinAt
  have hg_deriv : (Metric.ball c R₀).EqOn (deriv g) 0 :=
    fun z hz ↦ (hg_hasDeriv z hz).deriv
  have hc_mem : c ∈ Metric.ball c R₀ := mem_ball_self hR₀
  have h_id : riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch U w) = riemannZeta₁ c := by
    have h_eq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R₀).isPreconnected
      hg_diff hg_deriv hw hc_mem
    simpa [g, c] using h_eq
  have hc_ne : riemannZeta₁ c ≠ 0 := h_ne c hc_mem
  rw [eq_div_iff hc_ne]
  calc
    Complex.exp (logRiemannZeta₁Branch U w) * riemannZeta₁ c
      = Complex.exp (logRiemannZeta₁Branch U w) *
          (riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch U w)) := by rw [← h_id]
    _ = riemannZeta₁ w *
          (Complex.exp (logRiemannZeta₁Branch U w) * Complex.exp (-logRiemannZeta₁Branch U w)) := by
        ring
    _ = riemannZeta₁ w * 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    _ = riemannZeta₁ w := mul_one _

/-- General real-part upper bound for `logRiemannZeta₁Branch U` on `Metric.ball (2 + U * I) R₀`. -/
theorem re_logRiemannZeta₁Branch_le_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (hR₀ : 0 < R₀) (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    (logRiemannZeta₁Branch U w).re ≤ Real.log (3 * ‖riemannZeta₁ w‖) := by
  have h_norm := congrArg norm (exp_logRiemannZeta₁Branch_of_ne_zero hR₀ h_ne hw)
  rw [Complex.norm_exp, norm_div] at h_norm
  have h_re : (logRiemannZeta₁Branch U w).re =
      Real.log (‖riemannZeta₁ w‖ / ‖riemannZeta₁ (2 + (U : ℂ) * I)‖) := by
    rw [← h_norm, Real.log_exp]
  rw [h_re]
  have hw_pos : 0 < ‖riemannZeta₁ w‖ := norm_pos_iff.mpr (h_ne w hw)
  have hc_norm : 1 / 3 ≤ ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ :=
    one_third_le_norm_riemannZeta₁_of_re_eq_two (by simp)
  have hc_pos : 0 < ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ := by linarith
  refine Real.log_le_log (div_pos hw_pos hc_pos) ?_
  rw [div_le_iff₀ hc_pos]
  calc
    ‖riemannZeta₁ w‖ = 3 * ‖riemannZeta₁ w‖ * (1 / 3) := by ring
    _ ≤ 3 * ‖riemannZeta₁ w‖ * ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_left hc_norm (by positivity)

/-!
## Section 6: Borel–Carathéodory, FTC, and Cauchy Derivative Bounds Across `w.re = 1 / 2`
-/

/-- For `0 ≤ R ≤ 7 / 4` and `t : ℝ`,
`3 * zeta₁BallBound t R ≤ (14 * (1 + |t|)) ^ 2`. -/
theorem three_mul_zeta₁BallBound_le_sq_of_le_seven_fourths (t : ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hR_le : R ≤ 7 / 4) :
    3 * zeta₁BallBound t R ≤ (14 * (1 + |t|)) ^ 2 := by
  unfold zeta₁BallBound
  have h_norm1 : ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ 1 + |t| := by
    calc
      ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |t| := by simp
  have h_norm2 : ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  have h_div : (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R) ≤ 4 * (4 + |t|) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg t]
  have h_prod : (‖(1 : ℂ) + (t : ℂ) * I‖ + R) * (1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R)) ≤
      (3 + |t|) * (17 + 4 * |t|) := by
    refine mul_le_mul (by linarith) (by linarith)
      (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
      (by linarith [abs_nonneg t])
  nlinarith [abs_nonneg t, sq_nonneg |t|]

/-- For `0 ≤ R ≤ 7 / 4` and `t : ℝ`,
`Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (14 * (1 + |t|))`. -/
theorem log_three_mul_zeta₁BallBound_le_of_le_seven_fourths (t : ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hR_le : R ≤ 7 / 4) :
    Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (14 * (1 + |t|)) := by
  have h_pos : 0 < 3 * zeta₁BallBound t R := by
    linarith [one_le_zeta₁BallBound t hR (by linarith)]
  have h_le := Real.log_le_log h_pos (three_mul_zeta₁BallBound_le_sq_of_le_seven_fourths t hR hR_le)
  rwa [Real.log_pow, Nat.cast_ofNat] at h_le

/-- Under `RiemannHypothesis` and a zero-free gap `Δ` at height `U`,
for `0 ≤ r < R ≤ 3 / 2 + Δ ^ 2 / 4`
and `w ∈ Metric.closedBall (2 + U * I) r`,
`‖logRiemannZeta₁Branch U w‖ ≤ 2 * Real.log (3 * zeta₁BallBound U R) * r / (R - r)`. -/
theorem norm_logRiemannZeta₁Branch_le_of_gap (hRH : RiemannHypothesis) {U Δ r R : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hr : 0 ≤ r) (hrR : r < R) (hR_le : R ≤ 3 / 2 + Δ ^ 2 / 4)
    (hw : w ∈ Metric.closedBall (2 + (U : ℂ) * I) r) :
    ‖logRiemannZeta₁Branch U w‖ ≤
      2 * Real.log (3 * zeta₁BallBound U R) * r / (R - r) := by
  have hR_pos : 0 < R := hr.trans_lt hrR
  have hR_lt_two : R < 2 := by nlinarith
  have h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R, riemannZeta₁ z ≠ 0 :=
    fun z hz ↦ riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap
      (ball_subset_ball hR_le hz)
  have hf_diff : DifferentiableOn ℂ (logRiemannZeta₁Branch U) (Metric.ball (2 + (U : ℂ) * I) R) :=
    fun z hz ↦
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).differentiableAt.differentiableWithinAt
  have hf_re : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R,
      (logRiemannZeta₁Branch U z).re ≤ Real.log (3 * zeta₁BallBound U R) := by
    intro z hz
    refine (re_logRiemannZeta₁Branch_le_of_ne_zero hR_pos h_ne hz).trans ?_
    have hz_pos : 0 < ‖riemannZeta₁ z‖ := norm_pos_iff.mpr (h_ne z hz)
    refine Real.log_le_log (by positivity) ?_
    exact mul_le_mul_of_nonneg_left
      (norm_riemannZeta₁_le_zeta₁BallBound hR_pos.le hR_lt_two (ball_subset_closedBall hz))
      (by positivity)
  have hw_norm : ‖w - (2 + (U : ℂ) * I)‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball (2 + (U : ℂ) * I) R :=
    mem_ball_iff_norm.mpr (hw_norm.trans_lt hrR)
  have h_bc := borelCaratheodory_ball
    (log_three_mul_zeta₁BallBound_pos U hR_pos.le hR_lt_two)
    hf_diff hf_re hR_pos hw_ball (logRiemannZeta₁Branch_self U)
  refine h_bc.trans ?_
  have hM_pos : 0 ≤ 2 * Real.log (3 * zeta₁BallBound U R) :=
    mul_nonneg zero_le_two (log_three_mul_zeta₁BallBound_pos U hR_pos.le hR_lt_two).le
  exact div_le_div₀ (mul_nonneg hM_pos hr)
    (mul_le_mul_of_nonneg_left hw_norm hM_pos)
    (by linarith) (by linarith)

/-- Every point `(σ : ℂ) + (U : ℂ) * I` with `σ ∈ Set.Icc (1 / 2 : ℝ) 2` lies in
`Metric.closedBall (2 + (U : ℂ) * I) (3 / 2)`. -/
theorem mem_closedBall_three_halves_of_mem_Icc {U σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (σ : ℂ) + (U : ℂ) * I ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2) := by
  rw [mem_closedBall_iff_norm]
  have h_sub : (σ : ℂ) + (U : ℂ) * I - (2 + (U : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h_sub, norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hσ.2])]
  linarith [hσ.1]

/-- **Uniform Cauchy Derivative Bound on `deriv riemannZeta₁ / riemannZeta₁` Across `[1 / 2, 2]`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U`, for every
`w ∈ Metric.closedBall (2 + U * I) (3 / 2)` (and in particular for `w = σ + U * I` for all
`σ ∈ Set.Icc (1 / 2 : ℝ) 2`),
`‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤ (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|))`. -/
theorem norm_logDeriv_riemannZeta₁_le_of_gap (hRH : RiemannHypothesis) {U Δ : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hw : w ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2)) :
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) := by
  let c : ℂ := 2 + (U : ℂ) * I
  let r : ℝ := 3 / 2
  let ρ : ℝ := Δ ^ 2 / 16
  let R : ℝ := 3 / 2 + Δ ^ 2 / 8
  let R₀ : ℝ := 3 / 2 + Δ ^ 2 / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrρR : r + ρ < R := by dsimp [r, ρ, R]; nlinarith
  have hR_le : R ≤ R₀ := by dsimp [R, R₀]; nlinarith
  have h_ne : ∀ z ∈ Metric.ball c R₀, riemannZeta₁ z ≠ 0 :=
    fun z hz ↦ riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap hz
  have hw_norm : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball c R₀ :=
    mem_ball_iff_norm.mpr (by dsimp [r, R₀] at hw_norm ⊢; nlinarith)
  rw [← (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hw_ball).deriv]
  have h_sub_closed : Metric.closedBall w ρ ⊆ Metric.ball c R₀ := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    have h1 : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
    dsimp [r, ρ, R₀] at hw_norm hz ⊢
    nlinarith
  have hf_diff : DifferentiableOn ℂ (logRiemannZeta₁Branch U) (Metric.ball c R₀) :=
    fun z hz ↦
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).differentiableAt.differentiableWithinAt
  have hd : DiffContOnCl ℂ (logRiemannZeta₁Branch U) (Metric.ball w ρ) :=
    (hf_diff.mono (closure_ball_subset_closedBall.trans h_sub_closed)).diffContOnCl
  have h_sphere : ∀ z ∈ Metric.sphere w ρ,
      ‖logRiemannZeta₁Branch U z‖ ≤
        2 * Real.log (3 * zeta₁BallBound U R) * (r + ρ) / (R - (r + ρ)) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hz_closed : z ∈ Metric.closedBall c (r + ρ) := by
      rw [mem_closedBall_iff_norm]
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
        _ ≤ r + ρ := by linarith
    exact norm_logRiemannZeta₁Branch_le_of_gap hRH hΔ_pos hΔ_le hgap
      (by dsimp [r, ρ]; positivity) hrρR hR_le hz_closed
  have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd h_sphere
  refine h_cauchy.trans ?_
  have h_log_le := log_three_mul_zeta₁BallBound_le_of_le_seven_fourths U (R := R)
    (by dsimp [R]; positivity) (by dsimp [R]; nlinarith)
  have h_log_pos : 0 ≤ Real.log (3 * zeta₁BallBound U R) :=
    (log_three_mul_zeta₁BallBound_pos U (by dsimp [R]; positivity) (by dsimp [R]; nlinarith)).le
  have h_rρ : r + ρ ≤ 2 := by dsimp [r, ρ]; nlinarith
  have h_sub_R : R - (r + ρ) = Δ ^ 2 / 16 := by dsimp [r, ρ, R]; ring
  rw [div_div, h_sub_R]
  have h_denom : (Δ ^ 2 / 16) * ρ = Δ ^ 4 / 256 := by dsimp [ρ]; ring
  rw [h_denom]
  calc
    2 * Real.log (3 * zeta₁BallBound U R) * (r + ρ) / (Δ ^ 4 / 256)
      ≤ 2 * Real.log (3 * zeta₁BallBound U R) * 2 / (Δ ^ 4 / 256) := by gcongr
    _ = (1024 / Δ ^ 4) * Real.log (3 * zeta₁BallBound U R) := by
        have : Δ ^ 4 ≠ 0 := pow_ne_zero 4 hΔ_pos.ne'
        field_simp
        ring
    _ ≤ (1024 / Δ ^ 4) * (2 * Real.log (14 * (1 + |U|))) :=
        mul_le_mul_of_nonneg_left h_log_le (by positivity)
    _ = (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) := by ring

/-- **Uniform Bound on `‖deriv riemannZeta / riemannZeta‖` Across `σ ∈ [1 / 2, 2]`
at Zero-Free Height `U ≠ 0`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U ≠ 0`, for every
`σ ∈ Set.Icc (1 / 2 : ℝ) 2`,
`‖deriv riemannZeta (σ + U * I) / riemannZeta (σ + U * I)‖ ≤`
`(2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) + 1 / |U|`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_of_gap (hRH : RiemannHypothesis) {U Δ σ : ℝ}
    (hU : U ≠ 0) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) + 1 / |U| := by
  let w : ℂ := (σ : ℂ) + (U : ℂ) * I
  have hw_closed : w ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2) :=
    mem_closedBall_three_halves_of_mem_Icc hσ
  have hw_ball : w ∈ Metric.ball (2 + (U : ℂ) * I) (3 / 2 + Δ ^ 2 / 4) := by
    rw [mem_closedBall_iff_norm] at hw_closed
    rw [mem_ball_iff_norm]
    nlinarith
  have hz1 : riemannZeta₁ w ≠ 0 :=
    riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap hw_ball
  have hw1 : w ≠ 1 := by
    intro h
    have : w.im = (1 : ℂ).im := congrArg Complex.im h
    simp [w, hU] at this
  rw [logDeriv_riemannZeta_eq_sub hw1 hz1]
  have h_im_le : |U| ≤ ‖w - 1‖ := by
    have h_im : (w - 1).im = U := by simp [w]
    simpa [h_im] using abs_im_le_norm (w - 1)
  have h_inv_le : 1 / ‖w - 1‖ ≤ 1 / |U| :=
    div_le_div_of_nonneg_left zero_le_one (abs_pos.mpr hU) h_im_le
  have h_tri : ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖ ≤
      ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
    calc
      ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖
        ≤ ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ = ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
        rw [norm_div 1 (w - 1), norm_one]
  linarith [norm_logDeriv_riemannZeta₁_le_of_gap hRH hΔ_pos hΔ_le hgap hw_closed]

/-!
## Section 7: Pigeonhole Existence of a Zero-Free Height `U ∈ [T, T + 1]`
-/

/-- **Pigeonhole Existence of a Zero-Free Height in `[T, T + 1]`**:
For any finite set of heights `S : Finset ℝ` and any `T : ℝ`, there exists `U ∈ Set.Icc T (T + 1)`
such that every `γ ∈ S` satisfies `1 / (2 * (S.card + 1)) ≤ |γ - U|`. -/
theorem exists_zero_free_gap_in_Icc (S : Finset ℝ) (T : ℝ) :
    ∃ U ∈ Set.Icc T (T + 1),
      ∀ γ ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |γ - U| := by
  let N : ℕ := S.card + 1
  let Δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1))
  have hN_pos : 0 < (S.card : ℝ) + 1 := by positivity
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hN_mul : 2 * ((S.card : ℝ) + 1) * Δ = 1 := by
    dsimp [Δ]
    field_simp
  let u : ℕ → ℝ := fun k ↦ T + (2 * (k : ℝ) + 1) * Δ
  have hu_mem : ∀ k ∈ Finset.range N, u k ∈ Set.Icc T (T + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : (k : ℝ) + 1 ≤ (S.card : ℝ) + 1 := by exact_mod_cast hk
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    refine ⟨by dsimp [u]; nlinarith, ?_⟩
    dsimp [u]
    nlinarith
  by_contra! h_all
  have h_ex : ∀ k ∈ Finset.range N, ∃ γ ∈ S, |γ - u k| < Δ :=
    fun k hk ↦ h_all (u k) (hu_mem k hk)
  classical
  let f : ℕ → ℝ := fun k ↦ if h : ∃ γ ∈ S, |γ - u k| < Δ then h.choose else 0
  have hf_mem : ∀ k ∈ Finset.range N, f k ∈ S := by
    intro k hk
    simp only [f, h_ex k hk, ↓reduceDIte]
    exact (h_ex k hk).choose_spec.1
  have hf_dist : ∀ k ∈ Finset.range N, |f k - u k| < Δ := by
    intro k hk
    simp only [f, h_ex k hk, ↓reduceDIte]
    exact (h_ex k hk).choose_spec.2
  have hf_inj : (Finset.range N : Set ℕ).InjOn f := by
    intro k₁ hk₁ k₂ hk₂ h_eq
    rw [Finset.mem_coe] at hk₁ hk₂
    have hd₁ := hf_dist k₁ hk₁
    have hd₂ := hf_dist k₂ hk₂
    rw [← h_eq] at hd₂
    have h_diff_lt : |u k₁ - u k₂| < 2 * Δ := by
      calc
        |u k₁ - u k₂| = |(f k₁ - u k₂) - (f k₁ - u k₁)| := by ring_nf
        _ ≤ |f k₁ - u k₂| + |f k₁ - u k₁| := abs_sub _ _
        _ < Δ + Δ := add_lt_add hd₂ hd₁
        _ = 2 * Δ := by ring
    have h_u_diff : |u k₁ - u k₂| = 2 * |(k₁ : ℝ) - (k₂ : ℝ)| * Δ := by
      have h_sub : u k₁ - u k₂ = 2 * ((k₁ : ℝ) - (k₂ : ℝ)) * Δ := by dsimp [u]; ring
      rw [h_sub, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos hΔ_pos]
    rw [h_u_diff] at h_diff_lt
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h_ge1 : (1 : ℝ) ≤ (k₂ : ℝ) - (k₁ : ℝ) := by
        have : k₁ + 1 ≤ k₂ := hlt
        have : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast this
        linarith
      have h_abs_ge1 : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        exact h_ge1
      nlinarith
    · have h_ge1 : (1 : ℝ) ≤ (k₁ : ℝ) - (k₂ : ℝ) := by
        have : k₂ + 1 ≤ k₁ := hgt
        have : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast this
        linarith
      have h_abs_ge1 : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
        rw [abs_of_nonneg (by linarith)]
        exact h_ge1
      nlinarith
  have h_card := Finset.card_le_card_of_injOn f
    (fun k hk ↦ Finset.mem_coe.mpr (hf_mem k (Finset.mem_coe.mp hk))) hf_inj
  rw [Finset.card_range] at h_card
  omega

/-!
## Section 8: Local Zero Count Bound and Symmetric Zero-Free Height in `[T, T + 1]`
-/

/-- **Jensen's Inequality for `riemannZeta₁`**:
For any center `c : ℂ` with `riemannZeta₁ c ≠ 0` and radii `0 < |r| < |R|`, if
`‖riemannZeta₁ z‖ ≤ M` on `sphere c |R|` with `1 ≤ M`, then the divisor sum of zeros of
`riemannZeta₁` in `closedBall c |r|` is at most
`Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r)`. -/
theorem sum_divisor_riemannZeta₁_le {c : ℂ} {r R M : ℝ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (hc : riemannZeta₁ c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖riemannZeta₁ z‖ ≤ M) :
    ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u ≤
      Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r) :=
  (analyticOnNhd_riemannZeta₁ (closedBall c |R|)).sum_divisor_le r_pos r_lt_R hM hc f_bound

/-- Explicit upper bound on `‖riemannZeta₁ z‖` on the sphere `sphere c R` when `0 ≤ R < c.re`. -/
theorem norm_riemannZeta₁_le_on_sphere {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hcR : R < c.re) (hz : z ∈ sphere c R) :
    ‖riemannZeta₁ z‖ ≤
      1 + (‖c - 1‖ + R) * (1 + (‖c‖ + R) / (c.re - R)) := by
  rw [mem_sphere_iff_norm] at hz
  have hz_re : c.re - R ≤ z.re := by
    have h1 : (c - z).re ≤ ‖c - z‖ := re_le_norm (c - z)
    rw [norm_sub_rev, hz, sub_re] at h1
    linarith
  have hz_re_pos : 0 < z.re := by linarith
  have hz_norm : ‖z‖ ≤ ‖c‖ + R := by
    calc
      ‖z‖ = ‖c + (z - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ = ‖c‖ + R := by rw [hz]
  have hz_sub_one : ‖z - 1‖ ≤ ‖c - 1‖ + R := by
    calc
      ‖z - 1‖ = ‖(c - 1) + (z - c)‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖z - c‖ := norm_add_le _ _
      _ = ‖c - 1‖ + R := by rw [hz]
  have h_div : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) :=
    div_le_div₀ (by positivity) hz_norm (by linarith) hz_re
  refine (norm_riemannZeta₁_le hz_re_pos).trans ?_
  gcongr

end ConjectureMachines.Semantics.Riemann.HorizontalBounds
