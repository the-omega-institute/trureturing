/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Grading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Grading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite homogeneous reconstruction and orthogonal native spectral projections. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators TensorProduct

noncomputable section

def naturalProjector (D : LatticeData) (hu : IsUnit D.G.det) (level : ℕ) :
    Module.End ℂ (ActualTensor D hu) where
  toFun state := (coefficients D hu).symm
    ((coefficients D hu state).filter (fun exponent => occupationWeight D exponent = level))
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

theorem coefficient_projector (D : LatticeData) (hu : IsUnit D.G.det)
    (level : ℕ) (state : ActualTensor D hu) (exponent : Occupation D) :
    coefficients D hu (naturalProjector D hu level state) exponent =
      if occupationWeight D exponent = level then coefficients D hu state exponent else 0 := by
  simp [naturalProjector, Finsupp.filter_apply]

theorem projector_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (level : ℕ) (state : ActualTensor D hu) :
    naturalProjector D hu level state ∈ eigenspace D hu H (weightValue D level) := by
  rw [eigen_support_iff D hu H hHG hGH]
  intro exponent different
  have different_level : occupationWeight D exponent ≠ level := by
    intro equality
    exact different (congrArg (weightValue D) equality)
  simp [coefficient_projector, different_level]

theorem projector_on_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (level selected : ℕ) (state : ActualTensor D hu)
    (homogeneous : state ∈ eigenspace D hu H (weightValue D level)) :
    naturalProjector D hu selected state = if selected = level then state else 0 := by
  classical
  have support := (eigen_support_iff D hu H hHG hGH _ state).mp homogeneous
  apply (coefficients D hu).injective
  apply Finsupp.ext
  intro exponent
  rw [coefficient_projector]
  by_cases equal_levels : selected = level
  · subst selected
    by_cases aligned : occupationWeight D exponent = level
    · simp [aligned]
    · simp [aligned, support exponent (fun equality => aligned (weightValue_injective D equality))]
  · by_cases aligned : occupationWeight D exponent = selected
    · have different : weightValue D (occupationWeight D exponent) ≠ weightValue D level := by
        intro equality
        exact equal_levels (aligned.symm.trans (weightValue_injective D equality))
      simp [equal_levels, aligned, support exponent different]
    · simp [equal_levels, aligned]

theorem projector_composition (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (selected level : ℕ) (state : ActualTensor D hu) :
    naturalProjector D hu selected (naturalProjector D hu level state) =
      if selected = level then naturalProjector D hu level state else 0 :=
  projector_on_eigen D hu H hHG hGH level selected _ (projector_eigen D hu H hHG hGH _ _)

def supportedLevels (D : LatticeData) (hu : IsUnit D.G.det) (state : ActualTensor D hu) :
    Finset ℕ := (coefficients D hu state).support.image (occupationWeight D)

theorem finite_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) :
    (∑ level ∈ supportedLevels D hu state, naturalProjector D hu level state) = state := by
  classical
  apply (coefficients D hu).injective
  apply Finsupp.ext
  intro exponent
  simp only [map_sum, Finsupp.finsetSum_apply, coefficient_projector]
  by_cases zero : coefficients D hu state exponent = 0
  · simp [zero]
  · have member : occupationWeight D exponent ∈ supportedLevels D hu state := by
      exact Finset.mem_image.mpr ⟨exponent, Finsupp.mem_support_iff.mpr zero, rfl⟩
    simp [member]

theorem finite_directness (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (levels : Finset ℕ) (states : ℕ → ActualTensor D hu)
    (homogeneous : ∀ level ∈ levels, states level ∈ eigenspace D hu H (weightValue D level))
    (zero : ∑ level ∈ levels, states level = 0) :
    ∀ level ∈ levels, states level = 0 := by
  classical
  intro level member
  have projected := congrArg (naturalProjector D hu level) zero
  rw [map_sum, map_zero] at projected
  have collapse : (∑ selected ∈ levels, naturalProjector D hu level (states selected)) =
      states level := by
    calc
      _ = ∑ selected ∈ levels, if level = selected then states selected else 0 := by
        apply Finset.sum_congr rfl
        intro selected selected_member
        exact projector_on_eigen D hu H hHG hGH selected level _
          (homogeneous selected selected_member)
      _ = states level := by simp [member]
  exact collapse.symm.trans projected

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
