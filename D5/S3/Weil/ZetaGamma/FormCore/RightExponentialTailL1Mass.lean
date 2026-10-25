/- GID: D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-halfline-l1-mass)
   anchors: []
   utility: none
   digest: Literal half-line L1 tail integrability and exact outer mass with its original endpoint trace. -/

/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Canonical-placement candidate only; no native/build/acceptance was run.
The original public theorem statements and literal rightExponentialTail
are retained. This standalone module contains no inverse-B append.
-/

import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology Convolution

private theorem l1_integral_translate_halfline (f : ℝ → ℂ) (t : ℝ) :
    (∫ s : ℝ in Ioi 0, f (t + s)) = ∫ s : ℝ in Ioi t, f s := by
  calc
    (∫ s : ℝ in Ioi 0, f (t + s)) =
        ∫ s : ℝ, (Ioi (0 : ℝ)).indicator (fun x : ℝ => f (t + x)) s :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ s : ℝ, (Ioi t).indicator f (t + s) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        by_cases hs : 0 < s
        · have hts : t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_pos hs, if_pos hts]
        · have hts : ¬ t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_neg hs, if_neg hts]
    _ = ∫ s : ℝ, (Ioi t).indicator f s := integral_add_left_eq_self _ t
    _ = ∫ s : ℝ in Ioi t, f s := integral_indicator measurableSet_Ioi

private theorem l1_tail_weighted_eq (k : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    rightExponentialTail k u t =
      (Real.exp (k * t) : ℂ) *
        ∫ x : ℝ in Ioi t, (Real.exp (-k * x) : ℂ) * u x := by
  calc
    rightExponentialTail k u t =
        ∫ s : ℝ in Ioi 0,
          (Real.exp (k * t) : ℂ) *
            ((Real.exp (-k * (t + s)) : ℂ) * u (t + s)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        have he : (Real.exp (-k * s) : ℂ) =
            (Real.exp (k * t) : ℂ) * (Real.exp (-k * (t + s)) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]
          congr 2
          ring
        change (Real.exp (-k * s) : ℂ) * u (t + s) = _
        rw [he]
        ring
    _ = (Real.exp (k * t) : ℂ) *
        ∫ s : ℝ in Ioi 0, (Real.exp (-k * (t + s)) : ℂ) * u (t + s) :=
      integral_const_mul _ _
    _ = _ := congrArg (fun z : ℂ => (Real.exp (k * t) : ℂ) * z)
      (l1_integral_translate_halfline
        (fun x : ℝ => (Real.exp (-k * x) : ℂ) * u x) t)

/-- The actual tail is integrable on the positive half-line for every L1
input there. Its integral keeps the literal endpoint trace, rather than
assuming that trace vanishes. -/
theorem right_exponential_tail_l1_integrable_and_mass
    {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ)
    (hu : IntegrableOn u (Ioi (0 : ℝ))) :
    IntegrableOn (rightExponentialTail k u) (Ioi (0 : ℝ)) ∧
    (∫ t : ℝ in Ioi 0, rightExponentialTail k u t) =
      ((k⁻¹ : ℝ) : ℂ) *
        ((∫ t : ℝ in Ioi 0, u t) - rightExponentialTail k u 0) := by
  let G : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u
  let K : ℝ → ℂ := (Iic (0 : ℝ)).indicator
    (fun t : ℝ => (Real.exp (k * t) : ℂ))
  have hG : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hu
  have hK : Integrable K volume :=
    (integrable_indicator_iff measurableSet_Iic).2
      (integrableOn_exp_mul_Iic hk 0).ofReal
  have hKmass : (∫ t : ℝ, K t) = ((k⁻¹ : ℝ) : ℂ) := by
    dsimp only [K]
    rw [integral_indicator measurableSet_Iic, integral_complex_ofReal,
      integral_exp_mul_Iic hk 0]
    simp
  have hGmass : (∫ t : ℝ, G t) = ∫ t : ℝ in Ioi 0, u t :=
    integral_indicator measurableSet_Ioi
  have hconv (t : ℝ) :
      (K ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G) t =
        rightExponentialTail k G t := by
    change (∫ s : ℝ, K s * G (t - s)) = _
    calc
      (∫ s : ℝ, K s * G (t - s)) =
          ∫ s : ℝ in Iic 0, (Real.exp (k * s) : ℂ) * G (t - s) := by
        rw [← integral_indicator measurableSet_Iic]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          by_cases hs : s ∈ Iic (0 : ℝ) <;> simp [K, hs]
      _ = ∫ s : ℝ in Ioi 0, (Real.exp (k * (-s)) : ℂ) * G (t - (-s)) := by
        simpa only [neg_zero] using
          (integral_comp_neg_Ioi 0
            (fun s : ℝ => (Real.exp (k * s) : ℂ) * G (t - s))).symm
      _ = rightExponentialTail k G t := by
        simp only [rightExponentialTail, mul_neg, neg_mul, sub_neg_eq_add]
  have hRG : Integrable (rightExponentialTail k G) volume := by
    rw [← funext hconv]
    exact hK.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hG
  have hwhole :
      (∫ t : ℝ, rightExponentialTail k G t) =
        ((k⁻¹ : ℝ) : ℂ) * ∫ t : ℝ in Ioi 0, u t := by
    rw [← funext hconv,
      integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hK hG,
      hKmass, hGmass]
    rfl
  have hpositive (t : ℝ) (ht : 0 ≤ t) :
      rightExponentialTail k G t = rightExponentialTail k u t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hts : t + s ∈ Ioi (0 : ℝ) := by
      change 0 < t + s
      linarith [hs]
    simp only [G, Set.indicator_of_mem hts]
  have hnegative (t : ℝ) (ht : t ≤ 0) :
      rightExponentialTail k G t =
        (Real.exp (k * t) : ℂ) * rightExponentialTail k G 0 := by
    rw [l1_tail_weighted_eq]
    have he :
        (∫ x : ℝ in Ioi t, (Real.exp (-k * x) : ℂ) * G x) =
          ∫ x : ℝ in Ioi 0, (Real.exp (-k * x) : ℂ) * G x := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : 0 < x
        · have htx : t < x := lt_of_le_of_lt ht hx
          simp [Set.mem_Ioi, hx, htx]
        · simp [G, Set.mem_Ioi, hx]
    rw [he]
    congr 1
    simp only [rightExponentialTail, zero_add]
  have hleft :
      (∫ t : ℝ in Iic 0, rightExponentialTail k G t) =
        ((k⁻¹ : ℝ) : ℂ) * rightExponentialTail k G 0 := by
    calc
      _ = ∫ t : ℝ in Iic 0,
          (Real.exp (k * t) : ℂ) * rightExponentialTail k G 0 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
        exact hnegative t ht
      _ = _ := by
        rw [integral_mul_const, integral_complex_ofReal, integral_exp_mul_Iic hk 0]
        simp
  have hposae : rightExponentialTail k G =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      rightExponentialTail k u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpositive t ht.le
  refine ⟨hRG.integrableOn.congr hposae, ?_⟩
  have hparts := intervalIntegral.integral_Iic_add_Ioi
    hRG.integrableOn hRG.integrableOn (b := (0 : ℝ))
  rw [hleft, hwhole, integral_congr_ae hposae,
    hpositive 0 le_rfl] at hparts
  linear_combination hparts

end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

