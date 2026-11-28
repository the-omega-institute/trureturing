/- GID: D5/S3/OperatorAlgebra/VectorStateGNS
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The GNS Hilbert space of a vector functional is identified with its cyclic representation by extending the linear map from the pre-GNS space. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Operator.Extend

/-!
Omega original.

The GNS Hilbert space of a vector functional is identified with its cyclic
representation by extending the linear map from the pre-GNS space.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace.Completion

namespace Omega.OperatorAlgebra.VectorStateGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)

/-- The positive functional of a vector in a star representation. -/
def vectorFunctional : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => inner ℂ v (π a v)
      map_add' := fun a b => by simp [inner_add_right]
      map_smul' := fun z a => by simp [inner_smul_right] }
    (by
      intro a ha
      obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
      change 0 ≤ inner ℂ v (π (star b * b) v)
      rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
        mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
      rw [inner_self_eq_norm_sq_to_K]
      change 0 ≤ (Complex.ofReal ‖π b v‖) ^ 2
      rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (sq_nonneg _))

@[simp] theorem vectorFunctional_apply (a : A) :
    vectorFunctional π v a = inner ℂ v (π a v) := rfl

private def preOrbit : (vectorFunctional π v).PreGNS →ₗ[ℂ] H where
  toFun a := π ((vectorFunctional π v).ofPreGNS a) v
  map_add' a b := by simp
  map_smul' z a := by simp

private theorem preOrbit_norm (a : (vectorFunctional π v).PreGNS) :
    ‖preOrbit π v a‖ = ‖(a : (vectorFunctional π v).GNS)‖ := by
  rw [norm_coe]
  have h := (vectorFunctional π v).preGNS_norm_sq a
  rw [vectorFunctional_apply, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right] at h
  have h' := congrArg Complex.re h
  rw [← Complex.ofReal_pow, Complex.ofReal_re, ← RCLike.re_eq_complex_re,
    inner_self_eq_norm_sq (𝕜 := ℂ)] at h'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'.symm

private def orbitIsometry : (vectorFunctional π v).GNS →ₗᵢ[ℂ] H :=
  (preOrbit π v).extendOfIsometry
    (e := (toComplₗᵢ : (vectorFunctional π v).PreGNS →ₗᵢ[ℂ] _).toLinearMap)
    denseRange_coe (preOrbit_norm π v)

private theorem orbitIsometry_coe (a : (vectorFunctional π v).PreGNS) :
    orbitIsometry π v a = preOrbit π v a :=
  LinearMap.extendOfIsometry_eq _ _ _ a

/-- The unitary from the completed GNS space to the given cyclic representation. -/
def cyclicUnitary (hcyc : DenseRange (fun a : A => π a v)) :
    (vectorFunctional π v).GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (orbitIsometry π v) (by
    have hd : DenseRange (orbitIsometry π v) := hcyc.mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨((vectorFunctional π v).toPreGNS a : (vectorFunctional π v).GNS),
        by simp [orbitIsometry_coe, preOrbit]⟩)
    intro x
    change x ∈ Set.range (orbitIsometry π v)
    have hc := (orbitIsometry π v).isometry.isUniformInducing.isComplete_range.isClosed
    exact hc.closure_eq ▸ hd x)

theorem cyclicUnitary_vacuum (hcyc : DenseRange (fun a : A => π a v)) :
    cyclicUnitary π v hcyc ((vectorFunctional π v).toPreGNS 1) = v := by
  change orbitIsometry π v ((vectorFunctional π v).toPreGNS 1) = v
  simp [orbitIsometry_coe, preOrbit]

theorem cyclicUnitary_intertwines (hcyc : DenseRange (fun a : A => π a v))
    (a : A) (x : (vectorFunctional π v).GNS) :
    cyclicUnitary π v hcyc ((vectorFunctional π v).gnsStarAlgHom a x) =
      π a (cyclicUnitary π v hcyc x) := by
  change orbitIsometry π v ((vectorFunctional π v).gnsStarAlgHom a x) =
    π a (orbitIsometry π v x)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((orbitIsometry π v).continuous.comp ((vectorFunctional π v).gnsStarAlgHom a).continuous)
      ((π a).continuous.comp (orbitIsometry π v).continuous)
  | ih x =>
    change orbitIsometry π v ((vectorFunctional π v).gnsNonUnitalStarAlgHom a x) =
      π a (orbitIsometry π v x)
    rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, orbitIsometry_coe, orbitIsometry_coe]
    simp [preOrbit, PositiveLinearMap.leftMulMapPreGNS]

end Omega.OperatorAlgebra.VectorStateGNS
