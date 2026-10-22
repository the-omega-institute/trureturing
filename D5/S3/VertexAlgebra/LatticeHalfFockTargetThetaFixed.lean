/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Theta-fixed original coefficients act on ker(S+id) with physical L0 shifts. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockAllStateField LatticeHalfFockTargetThetaCoefficients
open LatticeHalfFockTargetTheta LatticeHalfFockThetaMonodromy
open LatticeHalfFockLZeroCovariance LatticeInvolution LatticeSugawaraConformal
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped TensorProduct

noncomputable section

theorem sigmaTensor_involutive (D : LatticeData) (hu : IsUnit D.G.det) :
    Function.Involutive (sigmaTensor D hu) := by
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [sigmaTensor_tmul, sigma_involutive D polynomial]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]

def targetTheta (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu ≃ₗ[ℂ] ActualTensor D hu :=
  LinearEquiv.ofInvolutive (sigmaTensor D hu) (sigmaTensor_involutive D hu)

def oddTarget (D : LatticeData) (hu : IsUnit D.G.det) : Submodule ℂ (ActualTensor D hu) :=
  LinearMap.ker (sigmaTensor D hu + LinearMap.id)

@[simp] theorem mem_oddTarget (D : LatticeData) (hu : IsUnit D.G.det)
    (vector : ActualTensor D hu) :
    vector ∈ oddTarget D hu ↔ sigmaTensor D hu vector = -vector := by
  simp [oddTarget, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

theorem Ytw_fixed_oddTarget (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (fixed : theta D source = source) (exponent : ℤ)
    (vector : ActualTensor D hu) (odd : vector ∈ oddTarget D hu) :
    (Ytw D hu source).coeff exponent vector ∈ oddTarget D hu := by
  rw [mem_oddTarget, Ytw_target_theta, fixed, (mem_oddTarget D hu vector).mp odd, map_neg]

def restrictedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) (exponent : ℤ) : Module.End ℂ (oddTarget D hu) where
  toFun vector := ⟨(Ytw D hu source.val).coeff exponent vector.val,
    Ytw_fixed_oddTarget D hu source.val ((mem_fixedSpace D source.val).mp source.property)
      exponent vector.val vector.property⟩
  map_add' first second := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff exponent |>.map_add first.val second.val
  map_smul' scalar vector := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff exponent |>.map_smul scalar vector.val

private theorem restrictedCoefficient_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) (vector : oddTarget D hu) (exponent : ℤ)
    (below : exponent < coefficientOrderMinimum D hu source.val vector.val -
      2 * (sourceWeightBound D source.val : ℤ)) :
    restrictedCoefficient D hu source exponent vector = 0 := by
  apply Subtype.ext
  exact Ytw_source_lower_truncation D hu source.val vector.val exponent below

def restrictedCoverField (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) : HVertexOperator ℤ ℂ (oddTarget D hu) (oddTarget D hu) :=
  HVertexOperator.of_coeff (restrictedCoefficient D hu source) (by
    intro vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨coefficientOrderMinimum D hu source.val vector.val -
      2 * (sourceWeightBound D source.val : ℤ), ?_⟩
    intro exponent member
    by_contra outside
    exact member (restrictedCoefficient_truncation D hu source vector exponent (by omega)))

private theorem restrictedCoefficient_odd (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) (exponent : ℤ) (odd : Odd exponent) :
    restrictedCoefficient D hu source exponent = 0 := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  change (Ytw D hu source.val).coeff exponent vector.val = 0
  rw [(Ytw_even_odd_selection D hu).1 source.val
    ((mem_fixedSpace D source.val).mp source.property) exponent odd]
  exact LinearMap.zero_apply _

def evenRestrictedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) (exponent : ℤ) : Module.End ℂ (oddTarget D hu) :=
  if Even exponent then restrictedCoefficient D hu source exponent else 0

theorem restrictedCover_even_coefficients (D : LatticeData) (hu : IsUnit D.G.det)
    (source : fixedSpace D) (exponent : ℤ) :
    (restrictedCoverField D hu source).coeff exponent =
      evenRestrictedCoefficient D hu source exponent := by
  simp only [restrictedCoverField, HVertexOperator.coeff_of_coeff, evenRestrictedCoefficient]
  split_ifs with even
  · rfl
  · exact restrictedCoefficient_odd D hu source exponent (Int.not_even_iff_odd.mp even)

def restrictedVacuum (D : LatticeData) : fixedSpace D :=
  ⟨LatticeAllStateField.vacuum D, (mem_fixedSpace D _).mpr (theta_vacuum D)⟩

theorem restrictedCover_vacuum (D : LatticeData) (hu : IsUnit D.G.det) :
    restrictedCoverField D hu (restrictedVacuum D) = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext exponent
  simp only [restrictedCoverField, HVertexOperator.coeff_of_coeff]
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  change (Ytw D hu (Finsupp.single 0 1)).coeff exponent vector.val = _
  rw [Ytw_vacuum]
  by_cases zero : exponent = 0 <;>
    simp [FieldNormalProduct.identityField, HVertexOperator.coeff_of_coeff, zero]

structure FixedNativeAction (D : LatticeData) (hu : IsUnit D.G.det) where
  cover : fixedSpace D → HVertexOperator ℤ ℂ (oddTarget D hu) (oddTarget D hu)
  originalCoefficients : ∀ (source : fixedSpace D) (exponent : ℤ) (vector : oddTarget D hu),
    (cover source |>.coeff exponent vector).val =
      (Ytw D hu source.val).coeff exponent vector.val
  oddCoefficients : ∀ (source : fixedSpace D) (exponent : ℤ), Odd exponent →
    (cover source).coeff exponent = 0
  vacuumIdentity : cover (restrictedVacuum D) = FieldNormalProduct.identityField

def originalFixedNativeAction (D : LatticeData) (hu : IsUnit D.G.det) : FixedNativeAction D hu where
  cover := restrictedCoverField D hu
  originalCoefficients source exponent vector := by
    simp only [restrictedCoverField, HVertexOperator.coeff_of_coeff]
    rfl
  oddCoefficients source exponent odd := by
    rw [restrictedCover_even_coefficients]
    simp [evenRestrictedCoefficient, Int.not_even_iff_odd.mpr odd]
  vacuumIdentity := restrictedCover_vacuum D hu

private theorem Ytw_integer_mode_weight (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (source : Carrier D) (sourceWeight targetWeight : ℂ)
    (homogeneousSource : sugawaraMode D matrixH 0 source = sourceWeight • source)
    (mode : ℤ) (vector : ActualTensor D hu)
    (homogeneousTarget : LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector =
      targetWeight • vector) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((Ytw D hu source).coeff (-2 * mode - 2) vector) =
      (targetWeight + sourceWeight - (mode : ℂ) - 1) •
        (Ytw D hu source).coeff (-2 * mode - 2) vector := by
  rw [Ytw_L0_covariance D hu matrixH hHG hGH, homogeneousSource, homogeneousTarget]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  push_cast
  module

def physicalHomogeneousCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (sourceWeight targetWeight : ℂ) (mode : ℤ)
    (source : ↥(fixedSpace D ⊓ Module.End.eigenspace (sugawaraMode D matrixH 0) sourceWeight)) :
    ↥(oddTarget D hu ⊓ Module.End.eigenspace
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0) targetWeight)
      →ₗ[ℂ] ↥(oddTarget D hu ⊓ Module.End.eigenspace
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0)
          (targetWeight + sourceWeight - (mode : ℂ) - 1)) where
  toFun vector := ⟨(Ytw D hu source.val).coeff (-2 * mode - 2) vector.val, by
    constructor
    · exact Ytw_fixed_oddTarget D hu source.val
        ((mem_fixedSpace D source.val).mp source.property.1) (-2 * mode - 2)
        vector.val vector.property.1
    · apply Module.End.mem_eigenspace_iff.mpr
      exact Ytw_integer_mode_weight D hu matrixH hHG hGH source.val sourceWeight targetWeight
        (Module.End.mem_eigenspace_iff.mp source.property.2) mode vector.val
        (Module.End.mem_eigenspace_iff.mp vector.property.2)⟩
  map_add' first second := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff (-2 * mode - 2) |>.map_add first.val second.val
  map_smul' scalar vector := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff (-2 * mode - 2) |>.map_smul scalar vector.val

#print axioms Ytw_fixed_oddTarget
#print axioms restrictedCover_even_coefficients
#print axioms restrictedCover_vacuum
#print axioms physicalHomogeneousCoefficient

end
end D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed
