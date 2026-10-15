/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/DirectSum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/DirectSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-integer spectral direct sum and coefficient projectors. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Integral
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators DirectSum

noncomputable section

abbrev IntegerComponents (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) := ⨁ value : ℤ, eigenspace D hu H (value : ℂ)

def integerAssembly (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    IntegerComponents D hu H →ₗ[ℂ] ActualTensor D hu :=
  DirectSum.coeLinearMap (fun value : ℤ => eigenspace D hu H (value : ℂ))

theorem integerAssembly_injective (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Function.Injective (integerAssembly D hu H) := by
  have independence := ((nativeL0 D hu H).eigenspaces_iSupIndep).comp
    (Int.cast_injective (α := ℂ))
  have native_independence : iSupIndep (fun value : ℤ => eigenspace D hu H (value : ℂ)) := by
    simpa only [Function.comp_def, Module.End.eigenspace_def, Module.End.one_eq_id,
      eigenspace] using independence
  exact native_independence.dfinsupp_lsum_injective

def integerDirectSumEquiv (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) : IntegerComponents D hu H ≃ₗ[ℂ] oddSector D hu :=
  (LinearEquiv.ofInjective (integerAssembly D hu H) (integerAssembly_injective D hu H)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [integerAssembly, DirectSum.range_coeLinearMap]
      exact integral_supremum D hu H hHG hGH rank24))

def integerFiniteSum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (components : IntegerComponents D hu H) :
    ActualTensor D hu := by
  classical
  exact components.sum (fun value state => state.val)

theorem integerDirectSumEquiv_value (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (components : IntegerComponents D hu H) :
    (integerDirectSumEquiv D hu H hHG hGH rank24 components).val =
      integerFiniteSum D hu H components := by
  classical
  change integerAssembly D hu H components = _
  exact DirectSum.coeLinearMap_eq_dfinsuppSum _ _

def integerProjector (D : LatticeData) (hu : IsUnit D.G.det) (value : ℤ) :
    Module.End ℂ (ActualTensor D hu) where
  toFun state := by
    classical
    exact (coefficients D hu).symm ((coefficients D hu state).filter
      (fun exponent => weightValue D (occupationWeight D exponent) = (value : ℂ)))
  map_add' left right := by
    classical
    apply (coefficients D hu).injective
    apply Finsupp.ext
    intro exponent
    simp only [map_add, LinearEquiv.apply_symm_apply, Finsupp.filter_apply, Finsupp.add_apply]
    split_ifs <;> simp
  map_smul' scalar state := by
    classical
    apply (coefficients D hu).injective
    apply Finsupp.ext
    intro exponent
    simp only [map_smul, LinearEquiv.apply_symm_apply, Finsupp.filter_apply,
      Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem coefficient_integerProjector (D : LatticeData) (hu : IsUnit D.G.det)
    (value : ℤ) (state : ActualTensor D hu) (exponent : Occupation D) :
    coefficients D hu (integerProjector D hu value state) exponent =
      if weightValue D (occupationWeight D exponent) = (value : ℂ)
        then coefficients D hu state exponent else 0 := by
  classical
  simp [integerProjector, Finsupp.filter_apply]

theorem integerProjector_on_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (value selected : ℤ) (state : eigenspace D hu H (value : ℂ)) :
    integerProjector D hu selected state.val = if selected = value then state.val else 0 := by
  classical
  have support := (eigen_support_iff D hu H hHG hGH _ state.val).mp state.property
  apply (coefficients D hu).injective
  apply Finsupp.ext
  intro exponent
  rw [coefficient_integerProjector]
  by_cases equality : selected = value
  · subst selected
    by_cases aligned : weightValue D (occupationWeight D exponent) = (value : ℂ)
    · simp [aligned]
    · simp [aligned, support exponent aligned]
  · by_cases aligned : weightValue D (occupationWeight D exponent) = (selected : ℂ)
    · have different : weightValue D (occupationWeight D exponent) ≠ (value : ℂ) := by
        intro matches_value
        exact equality (Int.cast_injective (aligned.symm.trans matches_value))
      simp [equality, aligned, support exponent different]
    · simp [equality, aligned]

theorem integerProjector_assembly (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (value : ℤ) (components : IntegerComponents D hu H) :
    integerProjector D hu value (integerAssembly D hu H components) = (components value).val := by
  classical
  induction components using DirectSum.induction_on with
  | zero => simp
  | add left right left_proof right_proof =>
      simp only [map_add, DirectSum.add_apply, Submodule.coe_add, left_proof, right_proof]
  | of selected state =>
      rw [integerAssembly, DirectSum.coeLinearMap_of, integerProjector_on_eigen D hu H hHG hGH]
      by_cases equality : value = selected
      · subst selected
        simp
      · simp [equality, DirectSum.of_eq_of_ne, Ne.symm equality]

theorem integer_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (state : oddSector D hu) :
    integerFiniteSum D hu H ((integerDirectSumEquiv D hu H hHG hGH rank24).symm state) =
      state.val := by
  rw [← integerDirectSumEquiv_value D hu H hHG hGH rank24,
    LinearEquiv.apply_symm_apply]

theorem integer_inverse_coordinate (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (state : oddSector D hu) (value : ℤ) :
    (((integerDirectSumEquiv D hu H hHG hGH rank24).symm state) value).val =
      integerProjector D hu value state.val := by
  have assembled : integerAssembly D hu H
      ((integerDirectSumEquiv D hu H hHG hGH rank24).symm state) = state.val := by
    calc
      _ = integerFiniteSum D hu H
          ((integerDirectSumEquiv D hu H hHG hGH rank24).symm state) := by
        classical
        exact DirectSum.coeLinearMap_eq_dfinsuppSum _ _
      _ = state.val := integer_reconstruction D hu H hHG hGH rank24 state
  rw [← integerProjector_assembly D hu H hHG hGH value, assembled]

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
