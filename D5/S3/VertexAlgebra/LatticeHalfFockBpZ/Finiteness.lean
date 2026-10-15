/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Finiteness
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Finiteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine finite native half-Fock energy fibers and complex-bilinear grade duality. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Sector
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockNativeSpectrum
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockIntegralOddFixedSector
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open scoped BigOperators

noncomputable section

private def boundedOccupationCode (D : LatticeData) (level : ℕ)
    (exponent : {exponent : Occupation D // occupationWeight D exponent ≤ level}) :
    Fin D.rank × Fin (level + 1) → Fin (level + 1) :=
  fun index => ⟨exponent.val (index.1, index.2.val), by
    have bound := Finsupp.le_weight (fun index : Index D => 2 * index.2 + 1)
      (s := (index.1, index.2.val)) (by omega) exponent.val
    change exponent.val (index.1, index.2.val) ≤ occupationWeight D exponent.val at bound
    omega⟩

private theorem boundedOccupationCode_injective (D : LatticeData) (level : ℕ) :
    Function.Injective (boundedOccupationCode D level) := by
  intro first second equality
  apply Subtype.ext
  apply Finsupp.ext
  intro index
  by_cases within : index.2 < level + 1
  · exact congrArg Fin.val (congrFun equality (index.1, ⟨index.2, within⟩))
  · have outside (exponent : {exponent : Occupation D // occupationWeight D exponent ≤ level}) :
        exponent.val index = 0 := by
      by_contra nonzero
      have bound := Finsupp.le_weight_of_ne_zero'
        (fun index : Index D => 2 * index.2 + 1) nonzero
      change 2 * index.2 + 1 ≤ occupationWeight D exponent.val at bound
      have total := exponent.property
      omega
    rw [outside first, outside second]

private theorem level_occupations_finite (D : LatticeData) (level : ℕ) :
    Finite {exponent : Occupation D // occupationWeight D exponent = level} := by
  have bounded : Finite {exponent : Occupation D // occupationWeight D exponent ≤ level} :=
    Finite.of_injective (boundedOccupationCode D level)
      (boundedOccupationCode_injective D level)
  letI := bounded
  apply Finite.of_injective
    (fun exponent : {exponent : Occupation D // occupationWeight D exponent = level} =>
      (⟨exponent.val, le_of_eq exponent.property⟩ :
        {exponent : Occupation D // occupationWeight D exponent ≤ level}))
  intro first second equality
  exact Subtype.ext (congrArg
    (fun exponent : {exponent : Occupation D // occupationWeight D exponent ≤ level} =>
      exponent.val) equality)

private def levelCoefficientMap (D : LatticeData) (native : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (level : ℕ) :
    eigenspace D native H (weightValue D level) →ₗ[ℂ]
      ({exponent : Occupation D // occupationWeight D exponent = level} → ActualGround D native) where
  toFun state exponent := coefficients D native state.val exponent.val
  map_add' first second := by
    ext exponent
    simp only [Submodule.coe_add, map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' scalar state := by
    ext exponent
    simp only [Submodule.coe_smul, map_smul, Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]

private theorem levelCoefficientMap_injective (D : LatticeData) (native : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (level : ℕ) : Function.Injective (levelCoefficientMap D native H level) := by
  intro first second equality
  apply Subtype.ext
  apply (coefficients D native).injective
  apply Finsupp.ext
  intro exponent
  by_cases same : occupationWeight D exponent = level
  · exact congrFun equality ⟨exponent, same⟩
  · have different : weightValue D (occupationWeight D exponent) ≠ weightValue D level :=
      fun equality => same (weightValue_injective D equality)
    rw [(eigen_support_iff D native H leftInverse rightInverse _ _).mp first.property
      exponent different,
      (eigen_support_iff D native H leftInverse rightInverse _ _).mp second.property
        exponent different]

theorem native_level_finite (D : LatticeData) (native : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (level : ℕ) : FiniteDimensional ℂ (eigenspace D native H (weightValue D level)) := by
  letI := level_occupations_finite D level
  letI := Fintype.ofFinite {exponent : Occupation D // occupationWeight D exponent = level}
  exact FiniteDimensional.of_injective (levelCoefficientMap D native H level)
    (levelCoefficientMap_injective D native H leftInverse rightInverse level)

theorem native_grade_finite (D : LatticeData) (native : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (value : ℂ) : FiniteDimensional ℂ (eigenspace D native H value) := by
  by_cases represented : ∃ level : ℕ, weightValue D level = value
  · obtain ⟨level, rfl⟩ := represented
    exact native_level_finite D native H leftInverse rightInverse level
  · have empty : eigenspace D native H value = ⊥ := by
      apply le_antisymm
      · intro state membership
        rw [Submodule.mem_bot]
        apply (coefficients D native).injective
        apply Finsupp.ext
        intro exponent
        change coefficients D native state exponent = 0
        apply (eigen_support_iff D native H leftInverse rightInverse _ _).mp membership
        intro equality
        exact represented ⟨occupationWeight D exponent, equality⟩
      · exact bot_le
    rw [empty]
    infer_instance

def gradePairing (H : Matrix (Fin data.rank) (Fin data.rank) ℂ) (value : ℂ) :
    LinearMap.BilinForm ℂ (eigenspace data determinantUnit H value) :=
  tensorPairing.compl₁₂ (eigenspace data determinantUnit H value).subtype
    (eigenspace data determinantUnit H value).subtype

theorem grade_pairing_nondegenerate (H : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : H * gramComplex data = 1) (rightInverse : gramComplex data * H = 1)
    (value : ℂ) : (gradePairing H value).Nondegenerate := by
  have separation := tensor_pairing_nondegenerate H leftInverse rightInverse
  have leftSeparating : (gradePairing H value).SeparatingLeft := by
    intro state radical
    apply Subtype.ext
    apply separation.1
    intro other
    rw [← finite_reconstruction data determinantUnit other, map_sum]
    apply Finset.sum_eq_zero
    intro level membership
    have projected := projector_eigen data determinantUnit H leftInverse rightInverse level other
    by_cases same : weightValue data level = value
    · rw [same] at projected
      exact radical ⟨naturalProjector data determinantUnit level other, projected⟩
    · exact native_grade_orthogonal H value (weightValue data level) (Ne.symm same)
        state.val (naturalProjector data determinantUnit level other) state.property projected
  constructor
  · exact leftSeparating
  · intro state radical
    apply leftSeparating
    intro other
    change tensorPairing state.val other.val = 0
    rw [tensor_pairing_symm.eq]
    exact radical other

def integralPairing (spectrum : LeechNativeSpectrum) (value : ℤ) :
    LinearMap.BilinForm ℂ (integralSector spectrum value) :=
  tensorPairing.compl₁₂ (integralSector spectrum value).subtype
    (integralSector spectrum value).subtype

theorem integral_grade_finite (spectrum : LeechNativeSpectrum) (value : ℤ) :
    FiniteDimensional ℂ (integralSector spectrum value) := by
  rw [integralSector_eq_native_eigenspace]
  exact native_grade_finite LeechData spectrum.native spectrum.inverse
    spectrum.leftInverse spectrum.rightInverse (value : ℂ)

theorem integral_pairing_nondegenerate (spectrum : LeechNativeSpectrum) (value : ℤ) :
    (integralPairing spectrum value).Nondegenerate := by
  unfold integralPairing
  rw [integralSector_eq_native_eigenspace]
  exact grade_pairing_nondegenerate spectrum.inverse spectrum.leftInverse
    spectrum.rightInverse (value : ℂ)

def integralSelfDuality (spectrum : LeechNativeSpectrum) (value : ℤ) :
    integralSector spectrum value ≃ₗ[ℂ] Module.Dual ℂ (integralSector spectrum value) := by
  letI := integral_grade_finite spectrum value
  exact (integralPairing spectrum value).toDual (integral_pairing_nondegenerate spectrum value)

theorem integral_self_duality_apply (spectrum : LeechNativeSpectrum) (value : ℤ)
    (first second : integralSector spectrum value) :
    integralSelfDuality spectrum value first second = tensorPairing first.val second.val := rfl

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
