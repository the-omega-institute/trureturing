/- GID: D5/S3/Weil/ZeroInfinitude/CosinePacket
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroInfinitude/CosinePacket
   mirror-E: none(waiver:kernel-verified-packet-and-finite-side-limits-only)
   anchors: []
   digest: A normalized convolution-square packet and its cosine-modulated finite-side limits. -/

import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
import D5.S3.Fourier.FourierLaplaceEntire
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaExplicit.ZeroSummability
import D5.S3.Weil.PrimePoleTerms
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Cosine-modulated packet

This is the packet half of the zero-infinitude argument in 增订三十. The
explicit formula `EF_lit` applies to every `ZeroConfig`, independently of the
cardinality of its carrier; this module proves only the normalized packet, its
cosine modulation, and the limits needed on a finite carrier.

The uniform prime bound uses the fixed support of the modulated packet, so it
needs neither Chebyshev estimates nor the prime number theorem. No assertion
about zeta zeros beyond the finite-carrier limit is made here, and this module
is not a proof of the Riemann hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set Topology
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped ComplexConjugate ContDiff FourierTransform

namespace D5.S3.Weil.ZeroInfinitude.CosinePacket

/-- The canonical normalized bump, regarded as a Weil packet seed. -/
def packetSeed : WeilTestFunction where
  toFun := fun x => (standardBump.normed volume x : Complex)
  contDiff' := Complex.ofRealCLM.contDiff.comp standardBump.contDiff_normed
  hasCompactSupport' := by
    change HasCompactSupport (Complex.ofRealCLM ∘ standardBump.normed volume)
    exact standardBump.hasCompactSupport_normed.comp_left (by simp)
  even' := by
    intro x
    exact_mod_cast standardBump.normed_neg x

/-- The seed has unit Fourier-Laplace transform at the origin. -/
theorem packetSeed_fourierLaplace_zero : fourierLaplace packetSeed 0 = 1 := by
  rw [fourierLaplace_apply]
  simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul]
  change (∫ x : Real, (standardBump.normed volume x : Complex)) = 1
  rw [integral_complex_ofReal]
  exact_mod_cast standardBump.integral_normed

/-- The positive-transform packet is the convolution square of the seed. -/
def packetSquare : WeilTestFunction := convolutionSquare packetSeed

/-- The packet transform is real and nonnegative on the real axis. -/
theorem packetTransform_real_nonneg (t : ℝ) :
    (Zeta23.paperFT (packetSquare : ℝ → ℂ) t).im = 0 ∧
      0 ≤ (Zeta23.paperFT (packetSquare : ℝ → ℂ) t).re := by
  rw [paperFT_eq_fourierLaplace]
  exact fourierLaplace_convolutionSquare_real_nonnegative packetSeed t

/-- The packet transform equals one at the origin. -/
theorem packetTransform_zero :
    Zeta23.paperFT (packetSquare : ℝ → ℂ) 0 = 1 := by
  rw [paperFT_eq_fourierLaplace, packetSquare]
  calc
    fourierLaplace (convolutionSquare packetSeed) 0 =
        (Complex.normSq (fourierLaplace packetSeed (0 : ℝ)) : ℂ) :=
      fourierLaplace_convolutionSquare_real packetSeed 0
    _ = 1 := by
      have hseed : fourierLaplace packetSeed ((0 : ℝ) : ℂ) = 1 := by
        simpa using packetSeed_fourierLaplace_zero
      rw [hseed]
      norm_num [Complex.normSq_apply]

/-- The packet transform is integrable on the real axis. -/
theorem packetTransform_integrable :
    Integrable (fun t : ℝ => Zeta23.paperFT (packetSquare : ℝ → ℂ) t) := by
  apply Zeta23.EF.integrable_paperFT_ofReal
  apply Zeta23.EF.integrable_fourier_of_contDiff_two
  · exact packetSquare.contDiff.of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)
  · exact packetSquare.hasCompactSupport

/-- The real part of the packet transform stays at least one half near zero. -/
theorem packetTransform_ge_half_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
      1 / 2 ≤ (Zeta23.paperFT (packetSquare : ℝ → ℂ) t).re := by
  let H : ℂ → ℂ := fun z => Zeta23.paperFT (packetSquare : ℝ → ℂ) z
  have hcontinuous : Continuous H := by
    convert (fourierLaplace_entire packetSquare).continuous using 1
    funext z
    exact paperFT_eq_fourierLaplace packetSquare z
  have hzero : H 0 = 1 := by
    simpa [H] using packetTransform_zero
  have hnear : H ⁻¹' Metric.ball (1 : ℂ) (1 / 2 : ℝ) ∈ nhds (0 : ℂ) := by
    apply hcontinuous.continuousAt
    simpa only [hzero] using
      Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε / 2, by positivity, ?_⟩
  intro t ht
  have htball : (t : ℂ) ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    calc
      |t| ≤ ε / 2 := ht
      _ < ε := by linarith
  have hHball : H (t : ℂ) ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) :=
    hball htball
  rw [Metric.mem_ball, Complex.dist_eq] at hHball
  have hre : |(H (t : ℂ) - 1).re| < (1 / 2 : ℝ) :=
    (Complex.abs_re_le_norm (H (t : ℂ) - 1)).trans_lt hHball
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith [neg_abs_le ((H (t : ℂ)).re - 1)]

/-- Multiplication by a real cosine preserves the Weil test-function class. -/
def cosineModulation (q : WeilTestFunction) (T : ℝ) : WeilTestFunction where
  toFun := fun x => (Real.cos (T * x) : ℂ) * q x
  contDiff' := by
    have hcos : ContDiff ℝ ∞ (fun x : ℝ => Real.cos (T * x)) :=
      Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
    exact (Complex.ofRealCLM.contDiff.comp hcos).mul q.contDiff
  hasCompactSupport' := q.hasCompactSupport.mul_left
  even' := by
    intro x
    rw [q.even, show T * (-x) = -(T * x) by ring, Real.cos_neg]

/-- Cosine modulation shifts the paper transform equally in both directions. -/
theorem paperFT_cosineModulation (q : WeilTestFunction) (T : ℝ) (z : ℂ) :
    Zeta23.paperFT (cosineModulation q T : ℝ → ℂ) z =
      (Zeta23.paperFT (q : ℝ → ℂ) (z + T) +
        Zeta23.paperFT (q : ℝ → ℂ) (z - T)) / 2 := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, Zeta23.paperFT_def]
  change (∫ x : ℝ, ((Real.cos (T * x) : ℂ) * q x) *
      Complex.exp (Complex.I * z * (x : ℂ))) = _
  have hplus : Integrable (fun x : ℝ =>
      q x * Complex.exp (Complex.I * (z + T) * (x : ℂ))) :=
    (q.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right
  have hminus : Integrable (fun x : ℝ =>
      q x * Complex.exp (Complex.I * (z - T) * (x : ℂ))) :=
    (q.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right
  rw [← integral_add hplus hminus, div_eq_mul_inv,
    ← Zeta23.integral_mul_const_C]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.ofReal_cos]
  field_simp
  calc
    Complex.cos ((T * x : ℝ) : ℂ) * q x *
          Complex.exp (Complex.I * z * (x : ℂ)) * 2 =
        (2 * Complex.cos ((T * x : ℝ) : ℂ)) * q x *
          Complex.exp (Complex.I * z * (x : ℂ)) := by ring
    _ = (Complex.exp (((T * x : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-((T * x : ℝ) : ℂ) * Complex.I)) * q x *
          Complex.exp (Complex.I * z * (x : ℂ)) := by
      rw [Complex.two_cos]
    _ = q x * (Complex.exp (Complex.I * (x : ℂ) * (z + (T : ℂ))) +
          Complex.exp (Complex.I * (x : ℂ) * (z - (T : ℂ)))) := by
      rw [show Complex.I * (x : ℂ) * (z + (T : ℂ)) =
          Complex.I * z * (x : ℂ) + ((T * x : ℝ) : ℂ) * Complex.I by
            push_cast; ring,
        show Complex.I * (x : ℂ) * (z - (T : ℂ)) =
          Complex.I * z * (x : ℂ) - ((T * x : ℝ) : ℂ) * Complex.I by
            push_cast; ring,
        Complex.exp_add, Complex.exp_sub]
      rw [div_eq_mul_inv, ← Complex.exp_neg]
      ring

private theorem decayMajorant_tendsto_zero (C a : ℝ) :
    Tendsto (fun T : ℝ => C / (1 + (T + a) ^ 2)) atTop (nhds 0) := by
  have hlinear : Tendsto (fun T : ℝ => T + a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_id
  have hsquare : Tendsto (fun u : ℝ => u ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left atTop 1 (hsquare.comp hlinear))

private theorem paperFT_shift_add_tendsto_zero (q : WeilTestFunction) (z : ℂ)
    (hz : |z.im| ≤ 1) :
    Tendsto (fun T : ℝ => Zeta23.paperFT (q : ℝ → ℂ) (z + T))
      atTop (nhds 0) := by
  obtain ⟨C, _hC, hdecay⟩ :=
    fourierLaplace_decay_closedStrip q 1 (by norm_num)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun T : ℝ => C / (1 + (T + z.re) ^ 2))
  · exact Eventually.of_forall fun T => norm_nonneg _
  · exact Eventually.of_forall fun T => by
      rw [paperFT_eq_fourierLaplace]
      have him : |(z + (T : ℂ)).im| ≤ 1 := by simpa
      simpa only [Complex.add_re, Complex.ofReal_re, add_zero, add_comm] using
        hdecay (z + (T : ℂ)) him
  · exact decayMajorant_tendsto_zero C z.re

private theorem paperFT_shift_sub_tendsto_zero (q : WeilTestFunction) (z : ℂ)
    (hz : |z.im| ≤ 1) :
    Tendsto (fun T : ℝ => Zeta23.paperFT (q : ℝ → ℂ) (z - T))
      atTop (nhds 0) := by
  obtain ⟨C, _hC, hdecay⟩ :=
    fourierLaplace_decay_closedStrip q 1 (by norm_num)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun T : ℝ => C / (1 + (T + (-z.re)) ^ 2))
  · exact Eventually.of_forall fun T => norm_nonneg _
  · exact Eventually.of_forall fun T => by
      rw [paperFT_eq_fourierLaplace]
      have him : |(z - (T : ℂ)).im| ≤ 1 := by simpa
      have hbound := hdecay (z - (T : ℂ)) him
      simpa only [Complex.sub_re, Complex.ofReal_re, sub_zero,
        show (z.re - T) ^ 2 = (T - z.re) ^ 2 by ring,
        show T - z.re = T + (-z.re) by ring] using hbound
  · exact decayMajorant_tendsto_zero C (-z.re)

/-- The modulated packet transform tends to zero at each point of the unit strip. -/
theorem paperFT_cosineModulation_tendsto_zero (z : ℂ) (hz : |z.im| ≤ 1) :
    Tendsto (fun T : ℝ =>
      Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ) z)
      atTop (nhds 0) := by
  have hplus := paperFT_shift_add_tendsto_zero packetSquare z hz
  have hminus := paperFT_shift_sub_tendsto_zero packetSquare z hz
  simpa [paperFT_cosineModulation] using
    (hplus.add hminus).div_const (2 : ℂ)

/-- The positive pole contribution of the modulated packet tends to zero. -/
theorem paperFT_cosineModulation_pole_pos_tendsto_zero :
    Tendsto (fun T : ℝ =>
      Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ)
        (Complex.I / 2)) atTop (nhds 0) := by
  apply paperFT_cosineModulation_tendsto_zero
  norm_num

/-- The negative pole contribution of the modulated packet tends to zero. -/
theorem paperFT_cosineModulation_pole_neg_tendsto_zero :
    Tendsto (fun T : ℝ =>
      Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ)
        (-Complex.I / 2)) atTop (nhds 0) := by
  apply paperFT_cosineModulation_tendsto_zero
  norm_num

open D5.S3.Weil.PrimePoleTerms

private theorem modulated_primeSummand_eq (q : WeilTestFunction) (T : ℝ) (n : ℕ) :
    (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (cosineModulation q T (Real.log n) +
        cosineModulation q T (-Real.log n))) =
      (Real.cos (T * Real.log n) : ℂ) * primeSummand q n := by
  rw [vonMangoldt_div_sqrt]
  rw [primeSummand]
  change (((ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((Real.cos (T * Real.log n) : ℂ) * q (Real.log n) +
        (Real.cos (T * (-Real.log n)) : ℂ) * q (-Real.log n))) = _
  rw [q.even, show T * -Real.log n = -(T * Real.log n) by ring, Real.cos_neg]
  push_cast
  ring

/-- The modulated prime term is bounded uniformly in the modulation frequency. -/
theorem primeTerm_cosineModulation_bounded :
    ∃ B : ℝ, ∀ T : ℝ,
      ‖∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n /
          Real.sqrt n : ℝ) : ℂ) *
        (cosineModulation packetSquare T (Real.log n) +
          cosineModulation packetSquare T (-Real.log n))‖ ≤ B := by
  let S : Finset ℕ := (primeSummand_hasFiniteSupport packetSquare).toFinset
  refine ⟨∑ n ∈ S, ‖primeSummand packetSquare n‖, fun T => ?_⟩
  rw [tsum_eq_sum (s := S) (fun n hn => by
    rw [modulated_primeSummand_eq]
    have hzero : primeSummand packetSquare n = 0 := by
      simpa [S] using hn
    rw [hzero, mul_zero])]
  calc
    ‖∑ n ∈ S, ((ArithmeticFunction.vonMangoldt n /
          Real.sqrt n : ℝ) : ℂ) *
        (cosineModulation packetSquare T (Real.log n) +
          cosineModulation packetSquare T (-Real.log n))‖
        ≤ ∑ n ∈ S, ‖((ArithmeticFunction.vonMangoldt n /
            Real.sqrt n : ℝ) : ℂ) *
          (cosineModulation packetSquare T (Real.log n) +
            cosineModulation packetSquare T (-Real.log n))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖primeSummand packetSquare n‖ := by
      gcongr with n hn
      rw [modulated_primeSummand_eq, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

/-- For a finite zero carrier, the full modulated zero side tends to zero. -/
theorem finiteCarrier_zeroSide_tendsto_zero (Z : Zeta23.ZeroConfig)
    (hZ : Z.carrier.Finite) :
    Tendsto (fun T : ℝ =>
      ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) *
        Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ)
          (Zeta23.gammaOf ρ)) atTop (nhds 0) := by
  letI : Fintype Z.carrier := hZ.fintype
  have hsum : Tendsto (fun T : ℝ =>
      ∑ ρ : Z.carrier, (Z.mult ρ : ℂ) *
        Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ)
          (Zeta23.gammaOf ρ)) atTop (nhds 0) := by
    have hterm : ∀ ρ ∈ (Finset.univ : Finset Z.carrier),
        Tendsto (fun T : ℝ => (Z.mult ρ : ℂ) *
          Zeta23.paperFT (cosineModulation packetSquare T : ℝ → ℂ)
            (Zeta23.gammaOf ρ)) atTop (nhds 0) := by
      intro ρ _hρ
      have hstrip := Z.strip (ρ : ℂ) ρ.property
      have hgamma : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 1 :=
        (Zeta23.WeilEF.abs_gammaOf_im_le hstrip).trans (by norm_num)
      have hmult : Tendsto (fun _ : ℝ => (Z.mult ρ : ℂ)) atTop
          (nhds (Z.mult ρ : ℂ)) := tendsto_const_nhds
      simpa using hmult.mul (paperFT_cosineModulation_tendsto_zero
        (Zeta23.gammaOf (ρ : ℂ)) hgamma)
    simpa using (tendsto_finset_sum Finset.univ hterm)
  simpa only [tsum_fintype] using hsum

-- The theorem domains and nontrivial hypotheses are inhabited in the pinned toolchain.
example : Nonempty WeilTestFunction := ⟨packetSeed⟩

example : |((0 : ℂ).im)| ≤ 1 := by norm_num

example : ∃ Z : Zeta23.ZeroConfig, Z.carrier.Finite := by
  refine ⟨{
    carrier := ∅
    mult := 0
    one_le_mult := by simp
    strip := by simp
    reflect_mem := by simp
    mult_reflect := by simp
    finite_window := by simp
  }, Set.finite_empty⟩

#print axioms packetSeed_fourierLaplace_zero
#print axioms packetTransform_real_nonneg
#print axioms packetTransform_zero
#print axioms packetTransform_integrable
#print axioms packetTransform_ge_half_near_zero
#print axioms paperFT_cosineModulation
#print axioms paperFT_cosineModulation_tendsto_zero
#print axioms paperFT_cosineModulation_pole_pos_tendsto_zero
#print axioms paperFT_cosineModulation_pole_neg_tendsto_zero
#print axioms primeTerm_cosineModulation_bounded
#print axioms finiteCarrier_zeroSide_tendsto_zero

end D5.S3.Weil.ZeroInfinitude.CosinePacket
