/- GID: D5/S3/Analysis/PlanarSublevelSandwich
   generality: G
   mirror-B: none(waiver:covered-by-planar-sublevel-sandwich-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth windows for the local sublevel of a planar map. -/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import OmegaBuild.Commands

/-!
Omega original.

Smooth windows for the local sublevel of a planar map.
-/

compile_only_with_mathlib

namespace Omega.Analysis.PlanarSublevelSandwich

open Filter Metric Set
open scoped Topology ContDiff

private theorem local_norm_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {z : E} (A : E ≃L[ℝ] E)
    (hf : HasFDerivAt f (A : E →L[ℝ] E) z) (hz : f z = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ x, dist x z < r →
      (1 - η) * ‖A (x - z)‖ ≤ ‖f x‖ ∧ ‖f x‖ ≤ (1 + η) * ‖A (x - z)‖ := by
  have h := hf.isEquivalent_sub A.toHomeomorph.isInducing
  have he := (Asymptotics.isLittleO_iff.mp h.isLittleO) hη
  simp only [Pi.sub_apply, hz, sub_zero] at he
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, hr, fun x hx => ?_⟩
  have he : ‖f x - A (x - z)‖ ≤ η * ‖A (x - z)‖ := hball hx
  constructor
  · have ht := norm_sub_norm_le (A (x - z)) (f x)
    rw [norm_sub_rev] at ht
    nlinarith only [ht, he]
  · have ht := norm_sub_norm_le (f x) (A (x - z))
    nlinarith only [ht, he]

private theorem local_scaled_ellipse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {z : E} (A : E ≃L[ℝ] E)
    (hf : HasFDerivAt f (A : E →L[ℝ] E) z) (hz : f z = 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ r > 0, ∀ ε > 0, ∀ u : E, ε * ‖u‖ < r →
      (‖A u‖ < (1 + η)⁻¹ → ‖f (z + ε • u)‖ < ε) ∧
      (‖f (z + ε • u)‖ < ε → ‖A u‖ < (1 - η)⁻¹) := by
  obtain ⟨r, hr, h⟩ := local_norm_bounds A hf hz hη
  refine ⟨r, hr, fun ε hε u hu => ?_⟩
  have hsub : z + ε • u - z = ε • u := add_sub_cancel_left z _
  have hdist : dist (z + ε • u) z < r := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact hu
  obtain ⟨hl, hh⟩ := h _ hdist
  rw [hsub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at hl hh
  have hplus : 0 < 1 + η := by linarith
  have hminus : 0 < 1 - η := by linarith
  constructor
  · intro hsmall
    have hm : ‖A u‖ * (1 + η) < 1 := (lt_div_iff₀ hplus).mp (by simpa only [one_div] using hsmall)
    calc
      ‖f (z + ε • u)‖ ≤ (1 + η) * (ε * ‖A u‖) := hh
      _ = ε * (‖A u‖ * (1 + η)) := by ring
      _ < ε := by simpa using mul_lt_mul_of_pos_left hm hε
  · intro hsmall
    have hm : ε * (‖A u‖ * (1 - η)) < ε := by
      calc
        _ = (1 - η) * (ε * ‖A u‖) := by ring
        _ ≤ ‖f (z + ε • u)‖ := hl
        _ < ε := hsmall
    rw [← one_div]
    apply (lt_div_iff₀ hminus).mpr
    exact lt_of_mul_lt_mul_left (by simpa using hm) hε.le


noncomputable section

open MeasureTheory

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem plane_ellipse_volume (A : Plane ≃L[ℝ] Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (A ⁻¹' ball 0 r) =
      Real.pi * r ^ 2 / |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)| := by
  have hdet := A.toLinearEquiv.isUnit_det'.ne_zero
  change volume.real ((A : Plane →L[ℝ] Plane) ⁻¹' ball 0 r) = _
  rw [Measure.real, Measure.addHaar_preimage_continuousLinearMap volume hdet,
    EuclideanSpace.volume_ball_fin_two]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_pos.le, abs_inv, div_eq_mul_inv]
  let d := |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹
  change d * (r ^ 2 * Real.pi) = Real.pi * r ^ 2 * d
  ac_rfl


private theorem bump_ellipse_integrals (A : Plane ≃L[ℝ] Plane) (b : ContDiffBump (0 : Plane)) :
    let d := |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)|
    Real.pi * b.rIn ^ 2 / d ≤ (∫ u : Plane, b (A u)) ∧
      (∫ u : Plane, b (A u)) ≤ Real.pi * b.rOut ^ 2 / d := by
  let ellipse (r : ℝ) := A ⁻¹' ball 0 r
  have hmeas (r : ℝ) : MeasurableSet (ellipse r) :=
    measurableSet_ball.preimage A.continuous.measurable
  have hfinite (r : ℝ) : volume (ellipse r) ≠ ⊤ := by
    change volume ((A : Plane →L[ℝ] Plane) ⁻¹' ball 0 r) ≠ ⊤
    rw [Measure.addHaar_preimage_continuousLinearMap volume A.toLinearEquiv.isUnit_det'.ne_zero,
      EuclideanSpace.volume_ball_fin_two]
    finiteness
  have hInt (r : ℝ) : Integrable ((ellipse r).indicator (1 : Plane → ℝ)) :=
    (integrableOn_const (C := (1 : ℝ)) (hfinite r)).integrable_indicator (hmeas r)
  have hB : Integrable (fun u : Plane => b (A u)) :=
    (b.contDiff (n := 0) |>.continuous.comp A.continuous).integrable_of_hasCompactSupport
      (b.hasCompactSupport.comp_homeomorph A.toHomeomorph)
  have hlo : (ellipse b.rIn).indicator (1 : Plane → ℝ) ≤ fun u => b (A u) := by
    intro u
    by_cases h : u ∈ ellipse b.rIn
    · change (ellipse b.rIn).indicator 1 u ≤ b (A u)
      have hx : A u ∈ closedBall (0 : Plane) b.rIn := ball_subset_closedBall h
      rw [indicator_of_mem h, Pi.one_apply, b.one_of_mem_closedBall hx]
    · rw [indicator_of_notMem h]
      exact b.nonneg
  have hhi : (fun u : Plane => b (A u)) ≤ (ellipse b.rOut).indicator (1 : Plane → ℝ) := by
    intro u
    by_cases h : u ∈ ellipse b.rOut
    · rw [indicator_of_mem h, Pi.one_apply]
      exact b.le_one
    · change b (A u) ≤ (ellipse b.rOut).indicator 1 u
      rw [indicator_of_notMem h, b.zero_of_le_dist (not_lt.mp h)]
  have hmlo := integral_mono (hInt b.rIn) hB hlo
  have hmhi := integral_mono hB (hInt b.rOut) hhi
  rw [integral_indicator_one (hmeas b.rIn), plane_ellipse_volume A b.rIn_pos.le] at hmlo
  rw [integral_indicator_one (hmeas b.rOut), plane_ellipse_volume A b.rOut_pos.le] at hmhi
  exact ⟨hmlo, hmhi⟩

/-- Fixed smooth planar windows bracket a small sublevel around a regular zero. -/
theorem smooth_local_ellipse_sandwich {f : Plane → Plane} {z : Plane}
    (A : Plane ≃L[ℝ] Plane) (hf : HasFDerivAt f (A : Plane →L[ℝ] Plane) z) (hz : f z = 0)
    {η ρ σ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hρ : 0 < ρ) (hρ' : ρ < (1 + η)⁻¹) (hσ : (1 - η)⁻¹ < σ) :
    let determinant := |LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)|
    ∃ (r : ℝ) (lower upper : Plane → ℝ), 0 < r ∧
      ContDiff ℝ ∞ lower ∧ ContDiff ℝ ∞ upper ∧
      HasCompactSupport lower ∧ HasCompactSupport upper ∧
      Real.pi * ρ ^ 2 / determinant ≤ (∫ u, lower u) ∧
      (∫ u, upper u) ≤ Real.pi * σ ^ 2 / determinant ∧
      ∀ ε > 0, ε * (‖(A.symm : Plane →L[ℝ] Plane)‖ * (1 + η)⁻¹) < r →
        ∀ u : Plane, lower u ≤ (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ∧
          (if ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε then 1 else 0) ≤ upper u := by
  classical
  obtain ⟨r, hr, hlocal⟩ := local_scaled_ellipse A hf hz hη hη1
  let lo : ContDiffBump (0 : Plane) := ⟨ρ, (1 + η)⁻¹, hρ, hρ'⟩
  let hi : ContDiffBump (0 : Plane) := ⟨(1 - η)⁻¹, σ, inv_pos.mpr (sub_pos.mpr hη1), hσ⟩
  refine ⟨r, lo ∘ A, hi ∘ A, hr, lo.contDiff.comp A.contDiff,
    hi.contDiff.comp A.contDiff, lo.hasCompactSupport.comp_homeomorph A.toHomeomorph,
    hi.hasCompactSupport.comp_homeomorph A.toHomeomorph,
    (bump_ellipse_integrals A lo).1, (bump_ellipse_integrals A hi).2, ?_⟩
  intro ε hε hcut u
  by_cases h : ε * ‖u‖ < r ∧ ‖f (z + ε • u)‖ < ε
  · have hu := (hlocal ε hε u h.1).2 h.2
    have hhi : hi (A u) = 1 := hi.one_of_mem_closedBall (by
      simpa [hi, Metric.mem_closedBall, dist_zero_right] using hu.le)
    simp only [h, ite_true, Function.comp_apply, hhi, le_refl, and_true]
    exact lo.le_one
  · have hu : (1 + η)⁻¹ ≤ ‖A u‖ := by
      by_contra! hsmall
      apply h
      have hinv := (A.symm : Plane →L[ℝ] Plane).le_opNorm (A u)
      have hle : ‖u‖ ≤ ‖(A.symm : Plane →L[ℝ] Plane)‖ * (1 + η)⁻¹ := by
        simpa using hinv.trans (mul_le_mul_of_nonneg_left hsmall.le (norm_nonneg _))
      have hnear := (mul_le_mul_of_nonneg_left hle hε.le).trans_lt hcut
      exact ⟨hnear, (hlocal ε hε u hnear).1 hsmall⟩
    have hlo : lo (A u) = 0 := lo.zero_of_le_dist (by
      simpa [lo, dist_zero_right] using hu)
    simp only [h, ite_false, Function.comp_apply, hlo, le_refl, true_and]
    exact hi.nonneg

end

end Omega.Analysis.PlanarSublevelSandwich
