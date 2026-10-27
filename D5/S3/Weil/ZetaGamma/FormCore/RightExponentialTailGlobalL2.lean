/- GID: D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-halfline-l2-mass-estimate)
   anchors: []
   utility: none
   digest: Split kernels control global actual right-tail L2 membership and squared mass. -/

import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate

/-! Global actual L2 control from a split kernel and the endpoint mass formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology

open private l2_tail_kernel_data l2_tail_translated_memLp from
  D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2

/-- The split-kernel square estimate has a globally integrable right side.
Unlike the plain translated-tail estimate it loses no first physical moment. -/
theorem right_exponential_tail_sq_le_tail_sq
    {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioi 0))) (t : ℝ) (ht : 0 ≤ t) :
    ‖rightExponentialTail k u t‖ ^ 2 ≤
      k⁻¹ * (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re := by
  let f : ℝ → ℂ := fun s => (Real.exp (-(k / 2) * s) : ℂ)
  let g : ℝ → ℂ := fun s => f s * u (t + s)
  obtain ⟨hf, hkernel⟩ := l2_tail_kernel_data (by linarith : 0 < k / 2)
  have hmass : (∫ s : ℝ in Ioi 0, ‖f s‖ ^ 2) = k⁻¹ := by
    convert hkernel using 1 <;> field_simp [hk.ne']
  have htranslate := l2_tail_translated_memLp u hu t ht
  have hg : MemLp g 2 (volume.restrict (Ioi 0)) := by
    apply htranslate.mono
      ((show Continuous f by dsimp [f]; fun_prop).aestronglyMeasurable.mul
        htranslate.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    have he : Real.exp (-(k / 2) * s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hk, hs])
    dsimp [g, f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) he
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Ioi 0)) (f := f) (g := g) hpq
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  rw [hmass] at hh
  have htail : rightExponentialTail k u t = ∫ s : ℝ in Ioi 0, f s * g s := by
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      have he : Real.exp (-k * s) =
          Real.exp (-(k / 2) * s) * Real.exp (-(k / 2) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp [f, g]
      rw [he, Complex.ofReal_mul]
      ring
  have hnorm : ‖rightExponentialTail k u t‖ ≤
      ∫ s : ℝ in Ioi 0, ‖f s‖ * ‖g s‖ := by
    rw [htail]
    simpa only [norm_mul] using norm_integral_le_integral_norm
      (fun s : ℝ => f s * g s) (μ := volume.restrict (Ioi 0))
  have hgmass : (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2) =
      (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re := by
    have he (s : ℝ) : ‖g s‖ ^ 2 = Real.exp (-k * s) * ‖u (t + s)‖ ^ 2 := by
      dsimp [g, f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    simp_rw [he]
    simp only [rightExponentialTail, ← Complex.ofReal_mul, integral_complex_ofReal,
      Complex.ofReal_re]
  calc
    _ ≤ (Real.sqrt k⁻¹ * Real.sqrt (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hh) 2
    _ = k⁻¹ * (∫ s : ℝ in Ioi 0, ‖g s‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hk.le),
        Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    _ = _ := by rw [hgmass]

/-- Actual L2 domain on the whole positive half-line. Measurability can be
supplied either by the L1 theorem for u, or by exponential conjugation from
the unweighted actual source. No L1 assumption on a weighted input is used. -/
theorem right_exponential_tail_memLp_two_and_mass_bound
    {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioi 0)))
    (hm : AEStronglyMeasurable (rightExponentialTail k u)
      (volume.restrict (Ioi 0))) :
    MemLp (rightExponentialTail k u) 2 (volume.restrict (Ioi 0)) ∧
      (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k u t‖ ^ 2) ≤
        (k⁻¹) ^ 2 * ∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2 := by
  have hsq : Integrable (fun x : ℝ => ‖u x‖ ^ (2 : ℕ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hsqC : IntegrableOn (fun x : ℝ => ((‖u x‖ ^ (2 : ℕ) : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
    change Integrable (fun x : ℝ => ((‖u x‖ ^ (2 : ℕ) : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ)))
    exact hsq.ofReal (𝕜 := ℂ)
  obtain ⟨hQ, hQmass⟩ := right_exponential_tail_l1_integrable_and_mass hk
    (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) hsqC
  have hs : IntegrableOn (fun t : ℝ => ‖rightExponentialTail k u t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
    apply (hQ.re.const_mul k⁻¹).mono' (hm.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact right_exponential_tail_sq_le_tail_sq hk u hu t ht.le
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 hs, ?_⟩
  have hzero : 0 ≤ (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) 0).re := by
    simp only [rightExponentialTail, zero_add, ← Complex.ofReal_mul,
      integral_complex_ofReal, Complex.ofReal_re]
    exact integral_nonneg fun s => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hQreal :
      (∫ t : ℝ in Ioi 0,
        (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re) =
      k⁻¹ * ((∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2) -
        (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) 0).re) := by
    have hre :
        (∫ t : ℝ in Ioi 0,
          (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re) =
        (∫ t : ℝ in Ioi 0,
          rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re hQ
    rw [hre, hQmass, integral_complex_ofReal]
    simp
  calc
    _ ≤ ∫ t : ℝ in Ioi 0,
        k⁻¹ * (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t).re := by
      apply integral_mono_ae hs (hQ.re.const_mul k⁻¹)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact right_exponential_tail_sq_le_tail_sq hk u hu t ht.le
    _ = k⁻¹ * (k⁻¹ * ((∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2) -
        (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) 0).re)) := by
      rw [integral_const_mul, hQreal]
    _ ≤ k⁻¹ * (k⁻¹ * ∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_self _ hzero) (inv_nonneg.mpr hk.le))
        (inv_nonneg.mpr hk.le)
    _ = _ := by ring

end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
