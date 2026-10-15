/- GID: D5/S3/VertexAlgebra/LatticeHalfFockIntegralOddFixedSector
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockIntegralOddFixedSector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine integral odd-target fixed-source graded action over the original Leech carrier. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixedVisible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeHalfFock
open D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open D5.S3.VertexAlgebra.LatticeActualConformalState
open D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentificationVisible
open D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta
open D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed
open D5.S3.VertexAlgebra.LatticeInvolution
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open scoped TensorProduct

noncomputable section

def integralSector (spectrum : LeechNativeSpectrum) (value : ℤ) :
    Submodule ℂ (ActualTensor LeechData spectrum.native) :=
  oddTarget LeechData spectrum.native ⊓
    Module.End.eigenspace (nativeL0 LeechData spectrum.native spectrum.inverse) (value : ℂ)

theorem oddTarget_eq_oddSector (spectrum : LeechNativeSpectrum) :
    oddTarget LeechData spectrum.native = oddSector LeechData spectrum.native := by
  rfl

theorem native_eigenspace_eq (spectrum : LeechNativeSpectrum) (value : ℤ) :
    Module.End.eigenspace (nativeL0 LeechData spectrum.native spectrum.inverse)
        (value : ℂ) =
      eigenspace LeechData spectrum.native spectrum.inverse (value : ℂ) := by
  apply le_antisymm
  · intro state membership
    change (nativeL0 LeechData spectrum.native spectrum.inverse -
      (value : ℂ) •
        (LinearMap.id : Module.End ℂ (ActualTensor LeechData spectrum.native))) state = 0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact sub_eq_zero.mpr (Module.End.mem_eigenspace_iff.mp membership)
  · intro state membership
    apply Module.End.mem_eigenspace_iff.mpr
    change (nativeL0 LeechData spectrum.native spectrum.inverse -
      (value : ℂ) •
        (LinearMap.id : Module.End ℂ (ActualTensor LeechData spectrum.native))) state = 0 at membership
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at membership
    exact sub_eq_zero.mp membership

theorem integralSector_eq_native_eigenspace (spectrum : LeechNativeSpectrum) (value : ℤ) :
    integralSector spectrum value =
      eigenspace LeechData spectrum.native spectrum.inverse (value : ℂ) := by
  unfold integralSector
  rw [native_eigenspace_eq]
  apply le_antisymm
  · intro state membership
    exact membership.2
  · intro state membership
    refine ⟨?_, membership⟩
    rw [oddTarget_eq_oddSector spectrum]
    exact integer_eigen_odd LeechData spectrum.native spectrum.inverse
      spectrum.leftInverse spectrum.rightInverse spectrum.rank24 value membership

theorem integralSector_below_two (spectrum : LeechNativeSpectrum) (value : ℤ)
    (below : value < 2) : integralSector spectrum value = ⊥ := by
  rw [integralSector_eq_native_eigenspace]
  exact integer_below_two LeechData spectrum.native spectrum.inverse
    spectrum.leftInverse spectrum.rightInverse spectrum.rank24 value below

theorem integralSector_supremum (spectrum : LeechNativeSpectrum) :
    (⨆ value : ℤ, integralSector spectrum value) =
      oddTarget LeechData spectrum.native := by
  calc
    (⨆ value : ℤ, integralSector spectrum value) =
        ⨆ value : ℤ,
          eigenspace LeechData spectrum.native spectrum.inverse (value : ℂ) := by
      apply iSup_congr
      intro value
      exact integralSector_eq_native_eigenspace spectrum value
    _ = oddSector LeechData spectrum.native :=
      integral_supremum LeechData spectrum.native spectrum.inverse
        spectrum.leftInverse spectrum.rightInverse spectrum.rank24
    _ = oddTarget LeechData spectrum.native := (oddTarget_eq_oddSector spectrum).symm

theorem native_weight_two_dimension (spectrum : LeechNativeSpectrum) :
    Module.finrank ℂ
      (eigenspace LeechData spectrum.native spectrum.inverse (2 : ℂ)) = 98304 :=
  spectrum.dimension

theorem native_weight_two_basis (spectrum : LeechNativeSpectrum) :
    ∀ label : Fin LeechData.rank ×
      LatticeTwistedGroundRealization.Half (groundRank LeechData spectrum.native),
      (spectrum.basis label).val =
        (MvPolynomial.X (label.1, 0) : Oscillator LeechData) ⊗ₜ[ℂ]
          (Pi.single label.2 (1 : ℂ) : ActualGround LeechData spectrum.native) :=
  spectrum.basisVectors

theorem literal_leech_native_stress (spectrum : LeechNativeSpectrum) :
    Ytw LeechData spectrum.native (omega LeechData spectrum.inverse) =
      tensorStressField LeechData (ActualGround LeechData spectrum.native)
        spectrum.inverse := by
  exact LatticeHalfFockConformalIdentificationVisible.Ytw_omega
    LeechData spectrum.native spectrum.inverse spectrum.leftInverse

def integralPhysicalMode (spectrum : LeechNativeSpectrum)
    (sourceWeight : ℂ) (value mode : ℤ)
    (source : ↥(fixedSpace LeechData ⊓
      Module.End.eigenspace (sugawaraMode LeechData spectrum.inverse 0) sourceWeight)) :
    integralSector spectrum value →ₗ[ℂ]
      ↥(oddTarget LeechData spectrum.native ⊓
        Module.End.eigenspace
          (nativeL0 LeechData spectrum.native spectrum.inverse)
          ((value : ℂ) + sourceWeight - (mode : ℂ) - 1)) := by
  exact physicalHomogeneousCoefficient LeechData spectrum.native spectrum.inverse
    spectrum.leftInverse spectrum.rightInverse sourceWeight (value : ℂ) mode source

theorem integralPhysicalMode_originalCoefficient (spectrum : LeechNativeSpectrum)
    (sourceWeight : ℂ) (value mode : ℤ)
    (source : ↥(fixedSpace LeechData ⊓
      Module.End.eigenspace (sugawaraMode LeechData spectrum.inverse 0) sourceWeight))
    (vector : integralSector spectrum value) :
    (integralPhysicalMode spectrum sourceWeight value mode source vector).val =
      (Ytw LeechData spectrum.native source.val).coeff (-2 * mode - 2) vector.val := by
  change (Ytw LeechData spectrum.native source.val).coeff (-2 * mode - 2) vector.val = _
  rfl

theorem integralPhysicalMode_shift (spectrum : LeechNativeSpectrum)
    (sourceWeight : ℂ) (value mode target : ℤ)
    (source : ↥(fixedSpace LeechData ⊓
      Module.End.eigenspace (sugawaraMode LeechData spectrum.inverse 0) sourceWeight))
    (shift : (value : ℂ) + sourceWeight - (mode : ℂ) - 1 = (target : ℂ))
    (vector : integralSector spectrum value) :
    (integralPhysicalMode spectrum sourceWeight value mode source vector).val ∈
      integralSector spectrum target := by
  rw [integralSector]
  simpa only [shift] using
    (integralPhysicalMode spectrum sourceWeight value mode source vector).property

theorem fixed_source_physical_mode_even (spectrum : LeechNativeSpectrum)
    (source : fixedSpace LeechData) (mode : ℤ) :
    Even (-2 * mode - 2) := by
  exact ⟨-mode - 1, by ring⟩

theorem fixed_source_odd_cover_vanishes (spectrum : LeechNativeSpectrum)
    (source : fixedSpace LeechData) (exponent : ℤ) (odd : Odd exponent) :
    (restrictedCoverField LeechData spectrum.native source).coeff exponent = 0 := by
  rw [restrictedCover_even_coefficients]
  simp [evenRestrictedCoefficient, Int.not_even_iff_odd.mpr odd]

def explicitLeechFixedNativeAction :
    FixedNativeAction LeechData explicitLeechSpectrum.native :=
  originalFixedNativeAction LeechData explicitLeechSpectrum.native

end
end D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector
