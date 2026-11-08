/- GID: D5/S3/Quantum/Foundation/ProjectorRayDifferential
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ProjectorRayDifferential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinitesimal ray distance from the modulus-inner-product Fubini-Study angle. -/

import D5.S3.QuantumBounds.FubiniStudyRecordTime
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.NormNum

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
  rw [horizontal, InnerProductSpace.rankOne_apply, norm_sub_sq (𝕜 := ℂ)]
  simp only [norm_smul, hψ, mul_one, inner_smul_right]
  rw [← inner_conj_symm z ψ]
  simp only [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  change ‖z‖ ^ 2 - 2 * (‖inner ℂ ψ z‖ ^ 2) + ‖inner ℂ ψ z‖ ^ 2 = _
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
    simpa [q, Function.comp_def] using hq.tendsto.comp hgn
  have hlimit : Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 ‖horizontal ψ v‖) := by
    have hm : Tendsto (fun t : ℝ => q ‖g t‖ * (‖g t‖ / |t|))
        (𝓝[≠] 0) (𝓝 ‖horizontal ψ v‖) := by simpa using hqn.mul hn
    apply hm.congr'
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht
    rw [fs_angle_eq_arcsin_horizontal ψ (f t) hψ ht]
    change q ‖g t‖ * (‖g t‖ / |t|) = Real.arcsin ‖g t‖ / |t|
    by_cases hr : ‖g t‖ = 0
    · simp [hr]
    · simp [q, Function.update_of_ne hr, div_mul_div_cancel₀ hr]
  have hv : Real.sqrt (‖v‖ ^ 2 - ‖inner ℂ ψ v‖ ^ 2) = ‖horizontal ψ v‖ := by
    rw [← horizontal_norm_sq ψ v hψ, Real.sqrt_sq (norm_nonneg _)]
  simpa [hv] using hlimit

private def projectorVelocity (ψ v : E) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ ψ v + InnerProductSpace.rankOne ℂ v ψ

private theorem rank_one_bilinear : IsBoundedBilinearMap ℝ
    (fun p : E × E => InnerProductSpace.rankOne ℂ p.1 p.2) where
  add_left x y z := by ext w; simp [InnerProductSpace.rankOne_apply]
  smul_left c x y := by
    ext w
    change inner ℂ y w • (c • x) = c • (inner ℂ y w • x)
    exact smul_comm _ _ _
  add_right x y z := by ext w; simp [InnerProductSpace.rankOne_apply]
  smul_right c x y := by
    ext w
    change inner ℂ (c • y) w • x = c • (inner ℂ y w • x)
    rw [inner_smul_left_eq_smul, smul_assoc]
  bound := ⟨1, zero_lt_one, fun x y => by simp⟩

private theorem projector_curve_hasDerivAt {f : ℝ → E} {ψ v : E}
    (h₀ : f 0 = ψ) (hf : HasDerivAt f v 0) :
    HasDerivAt (fun t => InnerProductSpace.rankOne ℂ (f t) (f t))
      (projectorVelocity ψ v) 0 := by
  simpa [IsBoundedBilinearMap.toContinuousLinearMap_apply, h₀, projectorVelocity]
    using (rank_one_bilinear (E := E)).toContinuousLinearMap.hasDerivAt_of_bilinear
      (fun _ => hf) (fun _ => hf)

private theorem unit_curve_tangent {f : ℝ → E} {ψ v : E}
    (h₀ : f 0 = ψ) (hf : HasDerivAt f v 0)
    (hunit : ∀ᶠ t in 𝓝 (0 : ℝ), ‖f t‖ = 1) : (inner ℂ ψ v).re = 0 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hc : HasDerivAt (fun t => ‖f t‖ ^ 2) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
      (hunit.mono fun t ht => by simp [ht])
  have h := hf.norm_sq.unique hc
  change 2 * (inner ℂ (f 0) v).re = 0 at h
  rw [h₀] at h
  linarith

private theorem trace_projector_velocity [FiniteDimensional ℂ E]
    (ψ v : E) (hψ : ‖ψ‖ = 1) (ht : (inner ℂ ψ v).re = 0) :
    LinearMap.trace ℂ E ((InnerProductSpace.rankOne ℂ ψ ψ).toLinearMap.comp
      ((projectorVelocity ψ v).toLinearMap.comp (projectorVelocity ψ v).toLinearMap)) =
      ((‖horizontal ψ v‖ ^ 2 : ℝ) : ℂ) := by
  let D := projectorVelocity ψ v
  have hconj : inner ℂ v ψ = -inner ℂ ψ v := by
    rw [← inner_conj_symm v ψ]
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.neg_re, ht, neg_zero]
    · simp only [Complex.conj_im, Complex.neg_im]
  have ha : D ψ = horizontal ψ v := by
    simp [D, projectorVelocity, horizontal, InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hψ, hconj, sub_eq_add_neg, add_comm]
  have hs (x y : E) : inner ℂ x (D y) = inner ℂ (D x) y := by
    simp only [D, projectorVelocity, ContinuousLinearMap.add_apply,
      InnerProductSpace.rankOne_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  rw [LinearMap.trace_comp_comm']
  change LinearMap.trace ℂ E (((D.comp D).comp
    (InnerProductSpace.rankOne ℂ ψ ψ)).toLinearMap) = _
  rw [InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne]
  change inner ℂ ψ (D (D ψ)) = _
  rw [hs, ha, inner_self_eq_norm_sq_to_K]
  simp

/-- The original ray-distance speed is the square root of the real projector
tensor evaluated on the actual derivative of the moving rank-one projection.
The derivative is taken in the operator norm, not prescribed by a metric. -/
theorem fs_angle_speed_projector [FiniteDimensional ℂ E] {f : ℝ → E} {ψ v : E}
    (hψ : ‖ψ‖ = 1) (h₀ : f 0 = ψ) (hf : HasDerivAt f v 0)
    (hunit : ∀ᶠ t in 𝓝 (0 : ℝ), ‖f t‖ = 1) :
    let P := InnerProductSpace.rankOne ℂ ψ ψ
    let D := deriv (fun t => InnerProductSpace.rankOne ℂ (f t) (f t)) 0
    Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 (Real.sqrt (LinearMap.trace ℂ E
        (P.toLinearMap.comp (D.toLinearMap.comp D.toLinearMap))).re)) := by
  dsimp only
  rw [(projector_curve_hasDerivAt h₀ hf).deriv,
    trace_projector_velocity ψ v hψ (unit_curve_tangent h₀ hf hunit)]
  change Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
    (𝓝 (Real.sqrt (‖horizontal ψ v‖ ^ 2)))
  rw [horizontal_norm_sq ψ v hψ]
  exact fs_angle_speed hψ h₀ hf hunit

#print axioms fs_angle_speed
#print axioms fs_angle_speed_projector

end D5.S3.Quantum.Foundation.ProjectorRayDifferential
