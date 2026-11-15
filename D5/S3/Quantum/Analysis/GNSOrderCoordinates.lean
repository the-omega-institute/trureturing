/- GID: D5/S3/Quantum/Analysis/GNSOrderCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/GNSOrderCoordinates
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal]
   utility: none
   digest: Dominated positive functionals have canonical positive GNS commutant coordinates. -/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-! Classical order-Radon--Nikodym coordinates for the actual completed GNS.
This is a foundational supplier, not the full-curvature centralizer theorem.
No faithfulness, normalization, separability or nonzero hypothesis is imposed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace
open UniformSpace.Completion ContinuousLinearMap

namespace D5.S3.Quantum.Analysis.GNSOrderCoordinates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Order comparison on the positive cone, rather than pointwise on all complex inputs. -/
def Dominated (φ ψ : A →ₚ[ℂ] ℂ) : Prop := ∀ a, 0 ≤ a → φ a ≤ ψ a

/-- The unnormalized cyclic vector, also in a zero GNS space. -/
def cyclicVector (ψ : A →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.GNS)

private theorem orbit_eq (ψ : A →ₚ[ℂ] ℂ) (a : A) :
    ψ.gnsStarAlgHom a (cyclicVector ψ) = (ψ.toPreGNS a : ψ.GNS) := by
  change ψ.gnsNonUnitalStarAlgHom a ((ψ.toPreGNS 1) : ψ.GNS) = _
  simp [PositiveLinearMap.leftMulMapPreGNS]

private theorem dense_pre (ψ : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => (ψ.toPreGNS a : ψ.GNS)) :=
  UniformSpace.Completion.denseRange_coe.comp ψ.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

private theorem pre_norm_le (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (x : ψ.PreGNS) :
    ‖φ.toPreGNS (ψ.ofPreGNS x)‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp := h (star (ψ.ofPreGNS x) * ψ.ofPreGNS x) (star_mul_self_nonneg _)
  have hφ := congrArg Complex.re (φ.preGNS_norm_sq (φ.toPreGNS (ψ.ofPreGNS x)))
  have hψ := congrArg Complex.re (ψ.preGNS_norm_sq x)
  simpa only [← hφ, ← hψ, ← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] using (Complex.le_def.mp hp).1

private def preComparison (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    ψ.PreGNS →L[ℂ] φ.PreGNS :=
  (φ.toPreGNS.toLinearMap.comp ψ.ofPreGNS.toLinearMap).mkContinuous 1
    (fun x => by simpa using pre_norm_le φ ψ h x)

/-- The canonical comparison contraction, defined on pre-GNS and then completed. -/
def comparison (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) : ψ.GNS →L[ℂ] φ.GNS :=
  (preComparison φ ψ h).completion

private theorem comparison_coe (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    comparison φ ψ h (ψ.toPreGNS a : ψ.GNS) = (φ.toPreGNS a : φ.GNS) := by
  simp [comparison, preComparison]

/-- Domination controls the comparison map on the entire completion. -/
theorem comparison_norm_le (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    ‖comparison φ ψ h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa [comparison, preComparison] using pre_norm_le φ ψ h x

/-- Intertwining is proved on the dense pre-GNS range and extended by continuity. -/
theorem comparison_intertwines (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    comparison φ ψ h ∘L ψ.gnsStarAlgHom a =
      φ.gnsStarAlgHom a ∘L comparison φ ψ h := by
  apply ContinuousLinearMap.ext
  apply (dense_pre ψ).equalizer <;> try fun_prop
  intro b
  simp only [ContinuousLinearMap.comp_apply]
  change comparison φ ψ h (ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS b : ψ.GNS)) = _
  simp [comparison_coe, PositiveLinearMap.leftMulMapPreGNS,
    show φ.gnsStarAlgHom a = φ.gnsNonUnitalStarAlgHom a from rfl]

/-- Taking the adjoint at star a gives the reverse intertwining identity. -/
theorem comparison_adjoint_intertwines (φ ψ : A →ₚ[ℂ] ℂ)
    (h : Dominated φ ψ) (a : A) :
    (comparison φ ψ h).adjoint ∘L φ.gnsStarAlgHom a =
      ψ.gnsStarAlgHom a ∘L (comparison φ ψ h).adjoint := by
  have he := congrArg ContinuousLinearMap.adjoint (comparison_intertwines φ ψ h (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using he.symm

/-- The Radon--Nikodym operator is constructed, not assumed. -/
def coordinate (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) : ψ.GNS →L[ℂ] ψ.GNS :=
  (comparison φ ψ h).adjoint ∘L comparison φ ψ h

private theorem coordinate_inner (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a b : A) :
    inner ℂ (ψ.toPreGNS a : ψ.GNS) (coordinate φ ψ h (ψ.toPreGNS b : ψ.GNS)) =
      φ (star a * b) := by
  simp [coordinate, ContinuousLinearMap.adjoint_inner_right, comparison_coe,
    UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

/-- The constructed coordinate belongs to the positive commutant unit interval. -/
theorem coordinate_mem (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    0 ≤ coordinate φ ψ h ∧ coordinate φ ψ h ≤ 1 ∧
      ∀ a, Commute (coordinate φ ψ h) (ψ.gnsStarAlgHom a) := by
  have hp : (coordinate φ ψ h).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self _
  refine ⟨ContinuousLinearMap.nonneg_iff_isPositive.mpr hp, ?_, ?_⟩
  · rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    refine ⟨ContinuousLinearMap.isSymmetric_one.sub hp.isSymmetric, ?_⟩
    intro x
    have hn := (comparison φ ψ h).le_opNorm x
    have hb := comparison_norm_le φ ψ h
    have hs := (comparison φ ψ h).apply_norm_sq_eq_inner_adjoint_left x
    have hr := congrArg Complex.re hs
    simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
    simp only [ContinuousLinearMap.reApplyInnerSelf, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, inner_sub_left, map_sub]
    rw [show (inner ℂ x x).re = ‖x‖ ^ 2 from norm_sq_eq_re_inner.symm]
    change 0 ≤ ‖x‖ ^ 2 - (inner ℂ (coordinate φ ψ h x) x).re
    dsimp only [coordinate] at *
    nlinarith [norm_nonneg ((comparison φ ψ h) x), norm_nonneg x]
  · intro a
    change (comparison φ ψ h).adjoint ∘L comparison φ ψ h ∘L ψ.gnsStarAlgHom a = _
    rw [← ContinuousLinearMap.comp_assoc, comparison_intertwines,
      ContinuousLinearMap.comp_assoc, comparison_adjoint_intertwines]
    rfl

/-- Exact coefficient formula for the original positive functional. -/
theorem coordinate_represents (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    φ a = inner ℂ (cyclicVector ψ)
      (coordinate φ ψ h (ψ.gnsStarAlgHom a (cyclicVector ψ))) := by
  rw [orbit_eq]
  simpa [cyclicVector] using (coordinate_inner φ ψ h 1 a).symm

end D5.S3.Quantum.Analysis.GNSOrderCoordinates
