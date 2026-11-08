/- GID: D5/S3/Quantum/Foundation/ProjectorRayDifferential
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ProjectorRayDifferential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinitesimal ray distance from the modulus-inner-product Fubini-Study angle. -/

import D5.S3.QuantumBounds.FubiniStudyRecordTime
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
The angle is the existing `fsAngle`, namely arccos of the modulus of the
complex inner product. The orthogonal residual below is constructed from the
rank-one projection; it is not a definition of a metric.

For a differentiable unit-amplitude curve, the actual angle divided by elapsed
absolute parameter tends to the norm of its horizontal velocity. Unit norm is
required only in a neighbourhood of the base point. The statement is valid in
any complex inner product space, hence in the original two-dimensional H_J.

This is the infinitesimal-distance part of OmegaQ-020, Theorem 7.3. The original
right-multiplication Pauli representation, its differential-projector tensor,
the curvature of the Berry connection, and the global loop/Stokes/gauge bridge
are separate mathematical obligations. No global phase formula is asserted.
-/

noncomputable section
open Filter
open scoped Topology ComplexConjugate

namespace D5.S3.Quantum.Foundation.ProjectorRayDifferential

open D5.S3.QuantumBounds.FubiniStudyRecordTime (fsAngle)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The component orthogonal to the unit amplitude's complex line. -/
def horizontal (ψ z : E) : E := z - InnerProductSpace.rankOne ℂ ψ ψ z

private theorem horizontal_norm_sq (ψ z : E) (hψ : ‖ψ‖ = 1) :
    ‖horizontal ψ z‖ ^ 2 = ‖z‖ ^ 2 - ‖inner ℂ ψ z‖ ^ 2 := by
  rw [horizontal, InnerProductSpace.rankOne_apply, norm_sub_sq]
  simp only [norm_smul, hψ, mul_one, inner_smul_right]
  rw [← inner_conj_symm z ψ]
  simp only [Complex.mul_conj, Complex.ofReal_re]
  rw [Complex.normSq_eq_norm_sq]
  ring

private theorem fs_angle_eq_arcsin_horizontal (ψ z : E)
    (hψ : ‖ψ‖ = 1) (hz : ‖z‖ = 1) :
    fsAngle ψ z = Real.arcsin ‖horizontal ψ z‖ := by
  rw [fsAngle, Real.arccos_eq_arcsin (norm_nonneg _)]
  congr 1
  have he := horizontal_norm_sq ψ z hψ
  rw [hz, one_pow] at he
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

/-- The metric speed of a differentiable unit-amplitude curve, measured by the
original Fubini-Study angle. No gauge choice for the curve is required. -/
theorem fs_angle_speed {f : ℝ → E} {ψ v : E}
    (hψ : ‖ψ‖ = 1) (h₀ : f 0 = ψ) (hf : HasDerivAt f v 0)
    (hunit : ∀ᶠ t in 𝓝 (0 : ℝ), ‖f t‖ = 1) :
    Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 (Real.sqrt (‖v‖ ^ 2 - ‖inner ℂ ψ v‖ ^ 2))) := by
  let g : ℝ → E := fun t => horizontal ψ (f t)
  have hc : HasDerivAt (fun t => inner ℂ ψ (f t)) (inner ℂ ψ v) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) ψ).inner ℂ hf
  have hg : HasDerivAt g (horizontal ψ v) 0 := by
    exact hf.sub (hc.smul_const ψ)
  have hg₀ : g 0 = 0 := by
    simp [g, horizontal, h₀, inner_self_eq_norm_sq_to_K, hψ]
  have hn : Tendsto (fun t : ℝ => ‖g t‖ / |t|) (𝓝[≠] 0)
      (𝓝 ‖horizontal ψ v‖) := by
    simpa [slope, hg₀, norm_smul, Real.norm_eq_abs, abs_inv,
      div_eq_mul_inv, mul_comm] using hg.tendsto_slope.norm
  have ha : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  let q : ℝ → ℝ := Function.update (fun r => Real.arcsin r / r) 0 1
  have hq : ContinuousAt q 0 := by
    simpa [q] using ha.continuousAt_div
  have hgn : Tendsto (fun t => ‖g t‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa [hg₀] using hg.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  have hqn : Tendsto (fun t => q ‖g t‖) (𝓝[≠] 0) (𝓝 1) := by
    simpa [q] using hq.tendsto.comp hgn
  have hlimit : Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 ‖horizontal ψ v‖) := by
    apply (by simpa using hqn.mul hn).congr'
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht
    rw [fs_angle_eq_arcsin_horizontal ψ (f t) hψ ht]
    change q ‖g t‖ * (‖g t‖ / |t|) = Real.arcsin ‖g t‖ / |t|
    by_cases hr : ‖g t‖ = 0
    · simp [hr]
    · simp [q, Function.update_of_ne hr, div_mul_div_cancel₀ hr]
  have hv : Real.sqrt (‖v‖ ^ 2 - ‖inner ℂ ψ v‖ ^ 2) = ‖horizontal ψ v‖ := by
    rw [← horizontal_norm_sq ψ v hψ, Real.sqrt_sq (norm_nonneg _)]
  simpa [hv] using hlimit

#print axioms fs_angle_speed

end D5.S3.Quantum.Foundation.ProjectorRayDifferential
