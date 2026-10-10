/- GID: D5/S3/Arith/Robin/PrimePrefixOriginalALogLowerBound
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixOriginalALogLowerBound
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The original A minus k log k is a complete strictly positive curvature-weighted logarithmic tangent gap. -/

import D5.S3.Arith.Robin.PrimePrefixCurvatureMoments
import D5.S3.Arith.Robin.PrimePrefixOriginalShoulder
import Mathlib.Tactic

/-!
The full literal curvature mass, first and logarithmic moments, and exact
original A logarithmic binding are consumed from PrimePrefixCurvatureMoments.
Its positive curvature supplier is PrimePrefixPhiCurvature. The same original
A and k=C-1 are the public definitions from PrimePrefixOriginalShoulder.
The logarithmic tangent and strict positive-integral criterion are Mathlib
suppliers. This is the tangent-gap realization of actual-prefix theory §450.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace D5.S3.Arith.Robin.PrimePrefixOriginalALogLowerBound
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.PrimePrefixOriginalShoulder

/-- The literal curvature weighted by the logarithmic tangent gap at k*v=1. -/
def curvatureLogGap (v : ℝ) : ℝ :=
  (slopeExcess*v-1-Real.log (slopeExcess*v))*deriv (deriv actualPhi) v

private theorem excess_pos : 0 < slopeExcess := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have he := Real.add_one_le_exp Real.eulerMascheroniConstant
  dsimp [slopeExcess, eulerAmplitude]
  linarith

private theorem curvature_pos {v : ℝ} (hv : 0 < v) :
    0 < deriv (deriv actualPhi) v :=
  (D5.S3.Arith.Robin.PrimePrefixPhiCurvature.result.2.2 v hv).1

private theorem gap_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ curvatureLogGap v := by
  have hl := Real.log_le_sub_one_of_pos (mul_pos excess_pos hv)
  exact mul_nonneg (by linarith) (curvature_pos hv).le

private theorem gap_pos_on_tail {v : ℝ} (hv : 2/slopeExcess < v) :
    0 < curvatureLogGap v := by
  have hk := excess_pos
  have hvpos : 0 < v := (div_pos (by norm_num) hk).trans hv
  have hcancel : slopeExcess*(2/slopeExcess) = (2 : ℝ) := by
    field_simp [hk.ne'] <;> ring
  have hmul := mul_lt_mul_of_pos_left hv hk
  rw [hcancel] at hmul
  have hl := Real.log_lt_sub_one_of_pos (mul_pos hk hvpos)
    (show slopeExcess*v ≠ 1 by linarith)
  exact mul_pos (by linarith) (curvature_pos hvpos)

private theorem gap_point {v : ℝ} (hv : 0 < v) :
    curvatureLogGap v =
      (slopeExcess*(v*deriv (deriv actualPhi) v) -
        (1+Real.log slopeExcess)*deriv (deriv actualPhi) v) -
      Real.log v*deriv (deriv actualPhi) v := by
  unfold curvatureLogGap
  rw [Real.log_mul excess_pos.ne' hv.ne']
  ring

private theorem gap_integrable : IntegrableOn curvatureLogGap (Ioi (0 : ℝ)) := by
  have hb := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.1
  have hm := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.1
  have hl := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.1
  have hlinear := (hm.const_mul slopeExcess).sub
    (hb.const_mul (1+Real.log slopeExcess))
  apply IntegrableOn.congr_fun (hlinear.sub hl)
  · intro v hv
    simpa only [Pi.sub_apply] using (gap_point hv).symm
  · exact measurableSet_Ioi

private theorem gap_value :
    (∫ v : ℝ in Ioi 0, curvatureLogGap v) =
      originalA-slopeExcess*Real.log slopeExcess := by
  have hb := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.1
  have hm := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.1
  have hl := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.1
  have hmass : (∫ v : ℝ in Ioi 0, deriv (deriv actualPhi) v) = slopeExcess := by
    simpa only [slopeExcess, eulerAmplitude] using
      D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.1
  have hmoment := D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.1
  have hA : originalA = -(∫ v : ℝ in Ioi 0, Real.log v*deriv (deriv actualPhi) v) := by
    simpa only [originalA, eulerAmplitude] using
      D5.S3.Arith.Robin.PrimePrefixCurvatureMoments.result.2.2.2.2.2.1
  have hlinear := (hm.const_mul slopeExcess).sub
    (hb.const_mul (1+Real.log slopeExcess))
  have hs := integral_sub (hm.const_mul slopeExcess)
    (hb.const_mul (1+Real.log slopeExcess))
  have ht := integral_sub hlinear hl
  simp only [Pi.sub_apply] at hs ht
  calc
    _ = ∫ v : ℝ in Ioi 0,
        (slopeExcess*(v*deriv (deriv actualPhi) v) -
          (1+Real.log slopeExcess)*deriv (deriv actualPhi) v) -
        Real.log v*deriv (deriv actualPhi) v :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => gap_point hv)
    _ = slopeExcess*(∫ v : ℝ in Ioi 0, v*deriv (deriv actualPhi) v) -
        (1+Real.log slopeExcess)*(∫ v : ℝ in Ioi 0, deriv (deriv actualPhi) v) -
        (∫ v : ℝ in Ioi 0, Real.log v*deriv (deriv actualPhi) v) := by
      rw [ht, hs, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [hmoment, hmass, hA]
      ring

private theorem gap_integral_pos : 0 < ∫ v : ℝ in Ioi 0, curvatureLogGap v := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] curvatureLogGap := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    exact gap_nonneg hv
  have hsub : Ioi (2/slopeExcess) ⊆ Function.support curvatureLogGap ∩ Ioi 0 := by
    intro v hv
    have hpos := gap_pos_on_tail hv
    have hvpos : 0 < v := (div_pos (by norm_num) excess_pos).trans hv
    exact ⟨hpos.ne', hvpos⟩
  have hs : 0 < volume (Function.support curvatureLogGap ∩ Ioi 0) := by
    have ht : 0 < volume (Ioi (2/slopeExcess)) := by
      rw [Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    exact ht.trans_le (measure_mono hsub)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hn gap_integrable).2 hs

/-- The same original A has a complete positive Jensen gap and strict two-sided bounds. -/
theorem result :
    IntegrableOn curvatureLogGap (Ioi (0 : ℝ)) ∧
    (∫ v : ℝ in Ioi 0, curvatureLogGap v) =
      originalA-slopeExcess*Real.log slopeExcess ∧
    0 < (∫ v : ℝ in Ioi 0, curvatureLogGap v) ∧
    slopeExcess*Real.log slopeExcess < originalA ∧ originalA < 1/2 := by
  have hgap := gap_integral_pos
  have hvalue := gap_value
  have hlower : slopeExcess*Real.log slopeExcess < originalA := by
    rw [hvalue] at hgap
    linarith
  have hupper : originalA < 1/2 := by
    simpa only [originalA, eulerAmplitude] using
      D5.S3.Arith.Robin.PrimePrefixOriginalA.result.2.2
  exact ⟨gap_integrable, hvalue, hgap, hlower, hupper⟩

end D5.S3.Arith.Robin.PrimePrefixOriginalALogLowerBound
