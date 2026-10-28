/- GID: D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-halfline-kernel-estimate)
   anchors: []
   utility: none
   digest: Actual Bochner integration and the sharp translated tail mass estimate on arbitrary half-line L2 inputs. -/

import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology

private theorem l2_tail_kernel_data {k : ℝ} (hk : 0 < k) :
    MemLp (fun s : ℝ => (Real.exp (-k * s) : ℂ)) 2
      (volume.restrict (Ioi 0)) ∧
    (∫ s : ℝ in Ioi 0, ‖(Real.exp (-k * s) : ℂ)‖ ^ 2) =
      1 / (2 * k) := by
  have hsquare (s : ℝ) :
      ‖(Real.exp (-k * s) : ℂ)‖ ^ 2 = Real.exp ((-2 * k) * s) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    ring
  constructor
  · apply (memLp_two_iff_integrable_sq_norm
      (show Continuous (fun s : ℝ => (Real.exp (-k * s) : ℂ)) from by
        fun_prop).aestronglyMeasurable).2
    simp_rw [hsquare]
    exact (integrableOn_exp_mul_Ioi
      (a := -2 * k) (by linarith : -2 * k < 0) 0).integrable
  · simp_rw [hsquare]
    rw [integral_exp_mul_Ioi
      (a := -2 * k) (by linarith : -2 * k < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hk.ne']
    <;> ring

private theorem l2_tail_translated_memLp
    (u : ℝ → ℂ) (hu : MemLp u 2 (volume.restrict (Ioi 0)))
    (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun s : ℝ => u (t + s)) 2 (volume.restrict (Ioi 0)) := by
  let U : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hu
  have hwhole : MemLp (fun s : ℝ => U (t + s)) 2 volume :=
    hU.comp_measurePreserving (measurePreserving_add_left volume t)
  have hrestricted : MemLp (fun s : ℝ => U (t + s)) 2
      (volume.restrict (Ioi 0)) :=
    MemLp.mono_measure Measure.restrict_le_self hwhole
  have hae : (fun s : ℝ => U (t + s)) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => u (t + s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos : t + s ∈ Ioi (0 : ℝ) := by
      change 0 < t + s
      change 0 < s at hs
      linarith
    dsimp only [U]
    rw [Set.indicator_of_mem hpos]
  exact (memLp_congr_ae hae).1 hrestricted

/-- An arbitrary half-line L2 input gives the actual right exponential-tail
integral at every nonnegative point. The constant 1/(2*k) is the exact squared
L2 norm of its kernel, and the right side keeps the translated tail mass. -/
theorem right_exponential_tail_l2_integrable_and_sq_le
    {k : ℝ} (hk : 0 < k)
    (u : ℝ → ℂ) (hu : MemLp u 2 (volume.restrict (Ioi 0)))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun s : ℝ => (Real.exp (-k * s) : ℂ) * u (t + s))
      (volume.restrict (Ioi 0)) ∧
    ‖rightExponentialTail k u t‖ ^ 2 ≤
      (1 / (2 * k)) * (∫ x : ℝ in Ioi t, ‖u x‖ ^ 2) := by
  let f : ℝ → ℂ := fun s => (Real.exp (-k * s) : ℂ)
  let g : ℝ → ℂ := fun s => u (t + s)
  obtain ⟨hf, hkint⟩ := l2_tail_kernel_data hk
  have hg : MemLp g 2 (volume.restrict (Ioi 0)) :=
    l2_tail_translated_memLp u hu t ht
  have hprod : Integrable (fun s : ℝ => f s * g s)
      (volume.restrict (Ioi 0)) :=
    hf.integrable_mul hg
  refine ⟨hprod, ?_⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Ioi 0)) (f := f) (g := g)
    hpq (by simpa only [ENNReal.ofReal_ofNat] using hf)
      (by simpa only [ENNReal.ofReal_ofNat] using hg)
  simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  change (∫ s : ℝ in Ioi 0, ‖f s‖ ^ 2) = 1 / (2 * k) at hkint
  rw [hkint] at hh
  have hnorm :
      ‖rightExponentialTail k u t‖ ≤
        ∫ s : ℝ in Ioi 0, ‖f s‖ * ‖g s‖ := by
    simpa only [rightExponentialTail, f, g, norm_mul] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi 0))
        (fun s : ℝ => f s * g s))
  have hmass : 0 ≤ ∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have htranslate :
      (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2) =
        ∫ x : ℝ in Ioi t, ‖u x‖ ^ 2 := by
    change (∫ s : ℝ in Ioi 0, ‖u (t + s)‖ ^ 2) =
      ∫ x : ℝ in Ioi t, ‖u x‖ ^ 2
    calc
      (∫ s : ℝ in Ioi 0, ‖u (t + s)‖ ^ 2) =
          ∫ s : ℝ, (Ioi (0 : ℝ)).indicator
            (fun x : ℝ => ‖u (t + x)‖ ^ 2) s :=
        (integral_indicator measurableSet_Ioi).symm
      _ = ∫ s : ℝ, (Ioi t).indicator (fun x : ℝ => ‖u x‖ ^ 2) (t + s) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          by_cases hs : 0 < s
          · have hts : t < t + s := by linarith
            simp only [Set.indicator_apply, Set.mem_Ioi, if_pos hs, if_pos hts]
          · have hts : ¬ t < t + s := by linarith
            simp only [Set.indicator_apply, Set.mem_Ioi, if_neg hs, if_neg hts]
      _ = ∫ s : ℝ, (Ioi t).indicator (fun x : ℝ => ‖u x‖ ^ 2) s :=
        integral_add_left_eq_self _ t
      _ = ∫ s : ℝ in Ioi t, ‖u s‖ ^ 2 :=
        integral_indicator measurableSet_Ioi
  calc
    ‖rightExponentialTail k u t‖ ^ 2 ≤
        (Real.sqrt (1 / (2 * k)) *
          Real.sqrt (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hh) 2
    _ = (1 / (2 * k)) * (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hmass]
    _ = (1 / (2 * k)) * (∫ x : ℝ in Ioi t, ‖u x‖ ^ 2) := by
      rw [htranslate]

end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail


#print axioms D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.right_exponential_tail_l2_integrable_and_sq_le
