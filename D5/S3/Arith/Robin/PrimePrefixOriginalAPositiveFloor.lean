/- GID: D5/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixOriginalAPositiveFloor
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal exponential curvature floor leaves a positive full remainder whose logarithmic gap proves the original A exceeds one sixteenth. -/

/-
The consumed logarithmic-exponential integrability helper retains:
Copyright the PrimeNumberTheoremAnd contributors.
Released under the Apache License, Version 2.0.
NOTICE and the complete license: Library/notes/pntplus2026mertens.md.
Source: kimihiro64/PrimeNumberTheoremAnd, commit
6a380f0c4658c04a420a9eb00b1ed62a1e3fde01, IEANTN/Mertens.lean;
consumed through D5/S3/Weil/Mertens/Gamma.lean.
Modified by this module: copy only the original private full log-exp
integrability proof, rename its local lemma, and consume the existing
public Gamma log-integral identity instead of copying that identity.
-/

import D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor
import D5.S3.Arith.Robin.PrimePrefixCurvatureMoments
import D5.S3.Arith.Robin.PrimePrefixOriginalShoulder
import D5.S3.Weil.Mertens.Gamma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
The whole positive-axis literal curvature floor is consumed from
PrimePrefixCurvatureExponentialFloor. All full curvature moments and the
original two-piece logarithmic binding are consumed from the public result
of PrimePrefixCurvatureMoments; the original A and Euler amplitude are the
unchanged public definitions in PrimePrefixOriginalShoulder.

The near/tail dominated proof of the classical exponential log-integral
below is faithfully copied from the existing private helper in Mertens.Gamma.
Its public Gamma logarithmic integral and the Mathlib Euler derivative
identity pay the exact exponential logarithmic moment.

The new positive remainder keeps the complete axis and all its moments.
A strict logarithmic tangent gap proves the literal original A exceeds
gamma/2+(k-1/2)*log(2*k-1), hence one sixteenth. No remaining Robin signed
transport or RH endpoint is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.PrimePrefixOriginalShoulder
open D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor

namespace D5.S3.Arith.Robin.PrimePrefixOriginalAPositiveFloor

/-- Complete mass remaining after the exact half-exponential density is removed. -/
def remainderMass : ℝ := slopeExcess-1/2

/-- The full literal remainder weighted by its logarithmic tangent gap. -/
def remainderLogGap (v : ℝ) : ℝ :=
  (2*remainderMass*v-1-Real.log (2*remainderMass*v))*curvatureRemainder v

private theorem remainderMass_pos : 0 < remainderMass := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have he := Real.add_one_le_exp Real.eulerMascheroniConstant
  dsimp [remainderMass, slopeExcess, eulerAmplitude]
  linarith

private theorem exp_integrable :
    IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
  simpa only [neg_one_mul] using
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0)

private theorem exp_moment_integrable :
    IntegrableOn (fun v : ℝ => v*Real.exp (-v)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (by norm_num : 0 < (2 : ℝ))
  norm_num at h
  simpa only [mul_comm] using h

private theorem exp_moment_value :
    (∫ v : ℝ in Ioi 0, v*Real.exp (-v)) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by norm_num : 0 < (2 : ℝ)) (by norm_num : 0 < (1 : ℝ))
  norm_num at h
  exact h

private lemma log_exp_integrable :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep


private theorem remainder_integrable :
    IntegrableOn curvatureRemainder (Ioi (0 : ℝ)) := by
  exact D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.1.sub
    (exp_integrable.div_const 2)

private theorem remainder_moment_integrable :
    IntegrableOn (fun v : ℝ => v*curvatureRemainder v) (Ioi 0) := by
  have h := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.1.sub
    (exp_moment_integrable.div_const 2)
  apply h.congr_fun
  · intro v hv
    dsimp [curvatureRemainder]
    ring
  · exact measurableSet_Ioi

private theorem remainder_log_integrable :
    IntegrableOn (fun v : ℝ => Real.log v*curvatureRemainder v) (Ioi 0) := by
  have h := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.1.sub
    (log_exp_integrable.div_const 2)
  apply h.congr_fun
  · intro v hv
    dsimp [curvatureRemainder]
    ring
  · exact measurableSet_Ioi

private theorem remainder_mass :
    (∫ v : ℝ in Ioi 0, curvatureRemainder v) = remainderMass := by
  unfold curvatureRemainder
  rw [integral_sub D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.1
    (exp_integrable.div_const 2), integral_div,
    integral_exp_neg_Ioi_zero,
    D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.1]
  rfl

private theorem remainder_moment :
    (∫ v : ℝ in Ioi 0, v*curvatureRemainder v) = (1/2 : ℝ) := by
  have hfun : (fun v : ℝ => v*curvatureRemainder v) =
      (fun v : ℝ => v*deriv (deriv actualPhi) v-(v*Real.exp (-v))/2) := by
    funext v
    dsimp [curvatureRemainder]
    ring
  rw [hfun, integral_sub D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.1
    (exp_moment_integrable.div_const 2), integral_div,
    D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.1, exp_moment_value]
  norm_num

private theorem A_remainder_log :
    originalA = Real.eulerMascheroniConstant/2-
      (∫ v : ℝ in Ioi 0, Real.log v*curvatureRemainder v) := by
  have hA : originalA =
      -(∫ v : ℝ in Ioi 0, Real.log v*deriv (deriv actualPhi) v) := by
    simpa only [originalA, eulerAmplitude] using
      D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.2.1
  have hlog : (∫ v : ℝ in Ioi 0, Real.log v*Real.exp (-v)) =
      -Real.eulerMascheroniConstant := by
    rw [integral_log_mul_exp_neg_eq_deriv_Gamma]
    linarith [Real.eulerMascheroniConstant_eq_neg_deriv]
  have hfun : (fun v : ℝ => Real.log v*curvatureRemainder v) =
      (fun v : ℝ => Real.log v*deriv (deriv actualPhi) v-
        (Real.log v*Real.exp (-v))/2) := by
    funext v
    dsimp [curvatureRemainder]
    ring
  rw [hfun, integral_sub D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.1
    (log_exp_integrable.div_const 2), integral_div, hlog]
  linarith

private theorem gap_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ remainderLogGap v := by
  have hrpos := remainderMass_pos
  have hpos : 0 < 2*remainderMass*v := by positivity
  have hl := Real.log_le_sub_one_of_pos hpos
  have hr := (D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor.result.2.1 v hv).2
  exact mul_nonneg (by linarith) hr.le

private theorem gap_pos_on_tail {v : ℝ} (hv : 1/remainderMass < v) :
    0 < remainderLogGap v := by
  have hr := remainderMass_pos
  have hvpos : 0 < v := (div_pos zero_lt_one hr).trans hv
  have hcancel : remainderMass*(1/remainderMass) = (1 : ℝ) := by
    field_simp [hr.ne']
  have hm := mul_lt_mul_of_pos_left hv hr
  rw [hcancel] at hm
  have hpos : 0 < 2*remainderMass*v := by positivity
  have hl := Real.log_lt_sub_one_of_pos hpos
    (show 2*remainderMass*v ≠ 1 by nlinarith)
  exact mul_pos (by linarith)
    (D5.S3.Arith.Robin.PrimePrefixCurvatureExponentialFloor.result.2.1 v hvpos).2

private theorem gap_point {v : ℝ} (hv : 0 < v) :
    remainderLogGap v =
      (2*remainderMass*(v*curvatureRemainder v)-
        (1+Real.log (2*remainderMass))*curvatureRemainder v)-
      Real.log v*curvatureRemainder v := by
  unfold remainderLogGap
  rw [Real.log_mul (mul_pos zero_lt_two remainderMass_pos).ne' hv.ne']
  ring

private theorem gap_integrable :
    IntegrableOn remainderLogGap (Ioi (0 : ℝ)) := by
  have hlinear := (remainder_moment_integrable.const_mul (2*remainderMass)).sub
    (remainder_integrable.const_mul (1+Real.log (2*remainderMass)))
  apply IntegrableOn.congr_fun (hlinear.sub remainder_log_integrable)
  · intro v hv
    simpa only [Pi.sub_apply] using (gap_point hv).symm
  · exact measurableSet_Ioi

private theorem gap_value :
    (∫ v : ℝ in Ioi 0, remainderLogGap v) =
      originalA-Real.eulerMascheroniConstant/2-
        remainderMass*Real.log (2*remainderMass) := by
  have hlinear := (remainder_moment_integrable.const_mul (2*remainderMass)).sub
    (remainder_integrable.const_mul (1+Real.log (2*remainderMass)))
  have hs := integral_sub (remainder_moment_integrable.const_mul (2*remainderMass))
    (remainder_integrable.const_mul (1+Real.log (2*remainderMass)))
  have ht := integral_sub hlinear remainder_log_integrable
  simp only [Pi.sub_apply] at hs ht
  calc
    _ = ∫ v : ℝ in Ioi 0,
        (2*remainderMass*(v*curvatureRemainder v)-
          (1+Real.log (2*remainderMass))*curvatureRemainder v)-
        Real.log v*curvatureRemainder v :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => gap_point hv)
    _ = 2*remainderMass*(∫ v : ℝ in Ioi 0, v*curvatureRemainder v)-
        (1+Real.log (2*remainderMass))*(∫ v : ℝ in Ioi 0, curvatureRemainder v)-
        (∫ v : ℝ in Ioi 0, Real.log v*curvatureRemainder v) := by
      rw [ht, hs, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [remainder_moment, remainder_mass]
      linarith [A_remainder_log]

private theorem gap_integral_pos : 0 < ∫ v : ℝ in Ioi 0, remainderLogGap v := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] remainderLogGap := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    exact gap_nonneg hv
  have hsub : Ioi (1/remainderMass) ⊆ Function.support remainderLogGap ∩ Ioi 0 := by
    intro v hv
    have hpos := gap_pos_on_tail hv
    have hvpos : 0 < v := (div_pos zero_lt_one remainderMass_pos).trans hv
    exact ⟨hpos.ne', hvpos⟩
  have hs : 0 < volume (Function.support remainderLogGap ∩ Ioi 0) := by
    have ht : 0 < volume (Ioi (1/remainderMass)) := by
      rw [Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    exact ht.trans_le (measure_mono hsub)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hn gap_integrable).2 hs

private theorem A_strict_lower :
    Real.eulerMascheroniConstant/2+
      remainderMass*Real.log (2*remainderMass) < originalA := by
  have h := gap_integral_pos
  rw [gap_value] at h
  linarith

private theorem mul_log_lower {x : ℝ} (hx : 0 < x) :
    -1/Real.exp 1 ≤ x*Real.log x := by
  have hlog := Real.one_sub_inv_le_log_of_pos (mul_pos (Real.exp_pos 1) hx)
  rw [Real.log_mul (Real.exp_ne_zero 1) hx.ne', Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hx.le
  have hid : x*(Real.exp 1*x)⁻¹ = 1/Real.exp 1 := by
    field_simp [hx.ne', Real.exp_ne_zero 1]
  have hmclean : x-x*(Real.exp 1*x)⁻¹ ≤ x+x*Real.log x := by nlinarith [hm]
  rw [hid] at hmclean
  rw [neg_div]
  linarith

private theorem positive_numeric_reserve :
    (1/16 : ℝ) < originalA := by
  have h := mul_log_lower (mul_pos zero_lt_two remainderMass_pos)
  have hterm : -1/(2*Real.exp 1) ≤ remainderMass*Real.log (2*remainderMass) := by
    rw [mul_comm (2 : ℝ) (Real.exp 1), div_mul_eq_div_div]
    simp only [neg_div] at h ⊢
    linarith
  have he : (8/3 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hinv : 1/(2*Real.exp 1) < (3/16 : ℝ) := by
    apply (div_lt_iff₀ (mul_pos zero_lt_two (Real.exp_pos 1))).2
    linarith
  have hg := Real.one_half_lt_eulerMascheroniConstant
  simp only [neg_div] at hterm
  linarith [A_strict_lower]

/-- Complete positive remainder moments and a strict positive lower bound for the original A. -/
theorem result :
    0 < remainderMass ∧
    IntegrableOn curvatureRemainder (Ioi (0 : ℝ)) ∧
    IntegrableOn (fun v : ℝ => v*curvatureRemainder v) (Ioi 0) ∧
    IntegrableOn (fun v : ℝ => Real.log v*curvatureRemainder v) (Ioi 0) ∧
    (∫ v : ℝ in Ioi 0, curvatureRemainder v) = remainderMass ∧
    (∫ v : ℝ in Ioi 0, v*curvatureRemainder v) = (1/2 : ℝ) ∧
    originalA = Real.eulerMascheroniConstant/2-
      (∫ v : ℝ in Ioi 0, Real.log v*curvatureRemainder v) ∧
    IntegrableOn remainderLogGap (Ioi (0 : ℝ)) ∧
    (∫ v : ℝ in Ioi 0, remainderLogGap v) =
      originalA-Real.eulerMascheroniConstant/2-
        remainderMass*Real.log (2*remainderMass) ∧
    0 < (∫ v : ℝ in Ioi 0, remainderLogGap v) ∧
    Real.eulerMascheroniConstant/2+
      remainderMass*Real.log (2*remainderMass) < originalA ∧
    (1/16 : ℝ) < originalA ∧ originalA < (1/2 : ℝ) := by
  have hupper : originalA < (1/2 : ℝ) := by
    simpa only [originalA, eulerAmplitude] using
      D5.S3.Arith.Robin.PrimePrefixOriginalA.result.2.2
  exact ⟨remainderMass_pos, remainder_integrable, remainder_moment_integrable,
    remainder_log_integrable, remainder_mass, remainder_moment, A_remainder_log,
    gap_integrable, gap_value, gap_integral_pos, A_strict_lower,
    positive_numeric_reserve, hupper⟩

end D5.S3.Arith.Robin.PrimePrefixOriginalAPositiveFloor
